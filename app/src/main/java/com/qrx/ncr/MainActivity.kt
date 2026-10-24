package com.qrx.ncr

import android.app.Activity
import android.app.AlertDialog
import android.content.Context
import android.content.Intent
import android.graphics.Bitmap
import android.graphics.BitmapFactory
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.Typeface
import android.net.Uri
import android.os.Bundle
import android.text.InputType
import android.text.method.ScrollingMovementMethod
import android.util.Base64
import android.view.Gravity
import android.view.View
import android.view.ViewGroup
import android.widget.Button
import android.widget.EditText
import android.widget.ImageView
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.TextView
import android.widget.Toast
import org.json.JSONArray
import org.json.JSONObject
import java.util.UUID

// ============================================================
// QR ENCODER — byte mode, versions 1-9, error correction level M
// ============================================================
object QrEncoder {
    private val ECC_M = intArrayOf(10, 16, 26, 18, 24, 16, 18, 22, 22)
    private val BLOCKS_M = intArrayOf(1, 1, 1, 2, 2, 4, 4, 4, 5)
    private val FORMAT_M = intArrayOf(
        0x5412, 0x5125, 0x5E7C, 0x5B4B, 0x45F9, 0x40CE, 0x4F97, 0x4AA0
    )
    private val VERSION_INFO = intArrayOf(
        0, 0, 0, 0, 0, 0,
        0x07C94, 0x085BC, 0x09A99
    )

    private val GF_EXP = IntArray(512)
    private val GF_LOG = IntArray(256)
    init {
        var x = 1
        for (i in 0 until 255) {
            GF_EXP[i] = x
            GF_LOG[x] = i
            x = x shl 1
            if (x and 0x100 != 0) x = x xor 0x11D
        }
        for (i in 255 until 512) GF_EXP[i] = GF_EXP[i - 255]
    }

    private fun rawModules(ver: Int): Int {
        var r = (16 * ver + 128) * ver + 64
        if (ver >= 2) {
            val n = ver / 7 + 2
            r -= (25 * n - 10) * n - 55
            if (ver >= 7) r -= 36
        }
        return r
    }

    private fun dataCodewords(ver: Int): Int =
        rawModules(ver) / 8 - ECC_M[ver - 1] * BLOCKS_M[ver - 1]

    private fun chooseVersion(byteLen: Int): Int {
        for (v in 1..9) {
            val cap = dataCodewords(v) * 8
            val need = 4 + 8 + byteLen * 8
            if (need <= cap) return v
        }
        throw IllegalArgumentException("payload too long")
    }

    private fun gfMul(a: Int, b: Int): Int {
        if (a == 0 || b == 0) return 0
        return GF_EXP[GF_LOG[a] + GF_LOG[b]]
    }

    private fun rsGenerator(deg: Int): IntArray {
        val r = IntArray(deg)
        r[deg - 1] = 1
        var root = 1
        for (i in 0 until deg) {
            for (j in 0 until deg) {
                r[j] = gfMul(r[j], root)
                if (j + 1 < deg) r[j] = r[j] xor r[j + 1]
            }
            root = gfMul(root, 2)
        }
        return r
    }

    private fun rsEncode(data: IntArray, eccLen: Int): IntArray {
        val gen = rsGenerator(eccLen)
        val res = IntArray(eccLen)
        for (b in data) {
            val factor = b xor res[0]
            System.arraycopy(res, 1, res, 0, eccLen - 1)
            res[eccLen - 1] = 0
            for (i in 0 until eccLen) res[i] = res[i] xor gfMul(gen[i], factor)
        }
        return res
    }

    private fun appendBits(list: MutableList<Boolean>, value: Int, len: Int) {
        for (i in len - 1 downTo 0) list.add((value shr i) and 1 == 1)
    }

    private fun encodeData(bytes: ByteArray, ver: Int): List<Boolean> {
        val bits = mutableListOf<Boolean>()
        appendBits(bits, 4, 4)
        appendBits(bits, bytes.size, 8)
        for (b in bytes) appendBits(bits, b.toInt() and 0xFF, 8)
        val cap = dataCodewords(ver) * 8
        val term = minOf(4, cap - bits.size)
        repeat(term) { bits.add(false) }
        while (bits.size % 8 != 0) bits.add(false)
        var pad = true
        while (bits.size < cap) {
            appendBits(bits, if (pad) 0xEC else 0x11, 8)
            pad = !pad
        }
        return bits
    }

    private fun bitsToCodewords(bits: List<Boolean>, ver: Int): IntArray {
        val n = dataCodewords(ver)
        val cw = IntArray(n)
        for (i in 0 until n) {
            var b = 0
            for (j in 0 until 8) if (bits[i * 8 + j]) b = b or (1 shl (7 - j))
            cw[i] = b
        }
        return cw
    }

    private fun interleave(data: IntArray, ver: Int): IntArray {
        val numBlocks = BLOCKS_M[ver - 1]
        val eccLen = ECC_M[ver - 1]
        val total = data.size
        val shortSize = total / numBlocks
        val numLong = total % numBlocks

        val dataBlocks = mutableListOf<IntArray>()
        val eccBlocks = mutableListOf<IntArray>()
        var pos = 0
        for (i in 0 until numBlocks) {
            val size = shortSize + if (i >= numBlocks - numLong) 1 else 0
            val block = IntArray(size)
            System.arraycopy(data, pos, block, 0, size)
            pos += size
            dataBlocks.add(block)
            eccBlocks.add(rsEncode(block, eccLen))
        }
        val out = mutableListOf<Int>()
        val maxData = shortSize + if (numLong > 0) 1 else 0
        for (i in 0 until maxData) for (b in dataBlocks) if (i < b.size) out.add(b[i])
        for (i in 0 until eccLen) for (e in eccBlocks) out.add(e[i])
        return out.toIntArray()
    }

    private fun alignmentPositions(ver: Int): IntArray = when (ver) {
        1 -> intArrayOf()
        2 -> intArrayOf(6, 18)
        3 -> intArrayOf(6, 22)
        4 -> intArrayOf(6, 26)
        5 -> intArrayOf(6, 30)
        6 -> intArrayOf(6, 34)
        7 -> intArrayOf(6, 22, 38)
        8 -> intArrayOf(6, 24, 42)
        9 -> intArrayOf(6, 26, 46)
        else -> intArrayOf()
    }

    private fun placeFinder(
        m: Array<BooleanArray>, res: Array<BooleanArray>, row: Int, col: Int
    ) {
        for (dr in -1..7) for (dc in -1..7) {
            val rr = row + dr; val cc = col + dc
            if (rr < 0 || rr >= m.size || cc < 0 || cc >= m.size) continue
            res[rr][cc] = true
            val border = dr == 0 || dr == 6 || dc == 0 || dc == 6
            val inner = dr in 2..4 && dc in 2..4
            if (border || inner) m[rr][cc] = true
        }
    }

    private fun placeAlignment(
        m: Array<BooleanArray>, res: Array<BooleanArray>, row: Int, col: Int
    ) {
        for (dr in 0..4) for (dc in 0..4) {
            res[row + dr][col + dc] = true
            val border = dr == 0 || dr == 4 || dc == 0 || dc == 4
            val center = dr == 2 && dc == 2
            if (border || center) m[row + dr][col + dc] = true
        }
    }

    private fun placeVersionInfo(m: Array<BooleanArray>, res: Array<BooleanArray>, ver: Int) {
        if (ver < 7) return
        val v = VERSION_INFO[ver - 1]
        val size = m.size
        for (i in 0 until 18) {
            val bit = ((v shr i) and 1) == 1
            val trRow = i / 3
            val trCol = size - 11 + (i % 3)
            m[trRow][trCol] = bit
            res[trRow][trCol] = true
            val blRow = size - 11 + (i % 3)
            val blCol = i / 3
            m[blRow][blCol] = bit
            res[blRow][blCol] = true
        }
    }

    private fun placeMatrix(cw: IntArray, ver: Int): Pair<Array<BooleanArray>, Array<BooleanArray>> {
        val size = 17 + 4 * ver
        val m = Array(size) { BooleanArray(size) }
        val res = Array(size) { BooleanArray(size) }

        placeFinder(m, res, 0, 0)
        placeFinder(m, res, 0, size - 7)
        placeFinder(m, res, size - 7, 0)

        val aps = alignmentPositions(ver)
        for (r in aps) for (c in aps) {
            val topLeft = r == 6 && c == 6
            val topRight = r == 6 && c == size - 7
            val botLeft = r == size - 7 && c == 6
            if (topLeft || topRight || botLeft) continue
            placeAlignment(m, res, r - 2, c - 2)
        }

        for (i in 8 until size - 8) {
            m[6][i] = i % 2 == 0; res[6][i] = true
            m[i][6] = i % 2 == 0; res[i][6] = true
        }

        m[size - 8][8] = true; res[size - 8][8] = true

        for (i in 0 until 9) { res[8][i] = true; res[i][8] = true }
        for (i in 0 until 8) {
            res[8][size - 1 - i] = true
            res[size - 1 - i][8] = true
        }

        placeVersionInfo(m, res, ver)

        var bit = 0
        var col = size - 1
        var up = true
        while (col > 0) {
            if (col == 6) col--
            for (row in 0 until size) {
                val r = if (up) size - 1 - row else row
                for (k in 0..1) {
                    val c = col - k
                    if (res[r][c]) continue
                    if (bit < cw.size * 8) {
                        val bi = bit / 8
                        val bp = 7 - (bit % 8)
                        m[r][c] = ((cw[bi] shr bp) and 1) == 1
                        bit++
                    }
                }
            }
            up = !up
            col -= 2
        }

        return Pair(m, res)
    }

    private fun applyMask(m: Array<BooleanArray>, res: Array<BooleanArray>, mask: Int) {
        for (r in m.indices) for (c in m.indices) {
            if (res[r][c]) continue
            val inv = when (mask) {
                0 -> (r + c) % 2 == 0
                1 -> r % 2 == 0
                2 -> c % 3 == 0
                3 -> (r + c) % 3 == 0
                4 -> (r / 2 + c / 3) % 2 == 0
                5 -> (r * c) % 2 + (r * c) % 3 == 0
                6 -> ((r * c) % 2 + (r * c) % 3) % 2 == 0
                7 -> ((r + c) % 2 + (r * c) % 3) % 2 == 0
                else -> false
            }
            if (inv) m[r][c] = !m[r][c]
        }
    }

    private fun bitOf(x: Int, i: Int) = ((x shr i) and 1) == 1

    private fun placeFormat(m: Array<BooleanArray>, mask: Int) {
        val f = FORMAT_M[mask]
        val s = m.size

        // MSB (bit 14) -> (8,0), LSB (bit 0) -> (0,8) per spec
        m[8][0] = bitOf(f, 14); m[8][1] = bitOf(f, 13); m[8][2] = bitOf(f, 12)
        m[8][3] = bitOf(f, 11); m[8][4] = bitOf(f, 10); m[8][5] = bitOf(f, 9)
        m[8][7] = bitOf(f, 8); m[8][8] = bitOf(f, 7); m[7][8] = bitOf(f, 6)
        m[5][8] = bitOf(f, 5); m[4][8] = bitOf(f, 4); m[3][8] = bitOf(f, 3)
        m[2][8] = bitOf(f, 2); m[1][8] = bitOf(f, 1); m[0][8] = bitOf(f, 0)

        // Second copy: MSB -> (s-1,8), LSB -> (8,s-1)
        m[s - 1][8] = bitOf(f, 14); m[s - 2][8] = bitOf(f, 13); m[s - 3][8] = bitOf(f, 12)
        m[s - 4][8] = bitOf(f, 11); m[s - 5][8] = bitOf(f, 10); m[s - 6][8] = bitOf(f, 9)
        m[s - 7][8] = bitOf(f, 8)
        m[8][s - 8] = bitOf(f, 7); m[8][s - 7] = bitOf(f, 6); m[8][s - 6] = bitOf(f, 5)
        m[8][s - 5] = bitOf(f, 4); m[8][s - 4] = bitOf(f, 3); m[8][s - 3] = bitOf(f, 2)
        m[8][s - 2] = bitOf(f, 1); m[8][s - 1] = bitOf(f, 0)
    }

    fun encode(text: String): Array<BooleanArray> {
        val bytes = text.toByteArray(Charsets.UTF_8)
        val ver = chooseVersion(bytes.size)
        val bits = encodeData(bytes, ver)
        val cw = bitsToCodewords(bits, ver)
        val all = interleave(cw, ver)
        val (m, res) = placeMatrix(all, ver)
        applyMask(m, res, 0)
        placeFormat(m, 0)
        return m
    }

    fun renderBitmap(text: String, sizePx: Int): Bitmap? {
        val m = try { encode(text) } catch (e: Exception) { return null }
        val modules = m.size
        val quiet = 4
        val total = modules + quiet * 2
        val scale = (sizePx / total).coerceAtLeast(1)
        val bmpSize = total * scale
        val bmp = Bitmap.createBitmap(bmpSize, bmpSize, Bitmap.Config.ARGB_8888)
        val canvas = Canvas(bmp)
        canvas.drawColor(Color.WHITE)
        val black = Paint().apply { color = Color.BLACK; isAntiAlias = false }
        for (r in 0 until modules) for (c in 0 until modules) {
            if (m[r][c]) {
                val x = (c + quiet) * scale
                val y = (r + quiet) * scale
                canvas.drawRect(
                    x.toFloat(), y.toFloat(),
                    (x + scale).toFloat(), (y + scale).toFloat(), black
                )
            }
        }
        return bmp
    }
}

// ============================================================
// DATA MODELS
// ============================================================
data class MsgItem(val from: String, val text: String, val ts: Long)

data class Chan(
    val id: String,
    val name: String,
    val messages: MutableList<MsgItem> = mutableListOf()
)

data class VaultItem(val type: String, val name: String, val content: String)

data class Vault(
    val id: String,
    val name: String,
    val items: MutableList<VaultItem> = mutableListOf(),
    val received: Boolean = false
)

// ============================================================
// STORE
// ============================================================
object Store {
    private const val PREFS = "qrx_store_v1"
    private lateinit var ctx: Context

    val chans = mutableListOf<Chan>()
    val vaults = mutableListOf<Vault>()

    fun init(c: Context) {
        if (!::ctx.isInitialized) ctx = c.applicationContext
        load()
    }

    fun load() {
        val p = ctx.getSharedPreferences(PREFS, Context.MODE_PRIVATE)
        chans.clear(); vaults.clear()
        val cj = p.getString("chans", "[]") ?: "[]"
        val carr = JSONArray(cj)
        for (i in 0 until carr.length()) {
            val o = carr.getJSONObject(i)
            val c = Chan(o.getString("id"), o.getString("name"))
            val ma = o.optJSONArray("msgs") ?: JSONArray()
            for (j in 0 until ma.length()) {
                val mo = ma.getJSONObject(j)
                c.messages.add(MsgItem(mo.getString("f"), mo.getString("t"), mo.getLong("ts")))
            }
            chans.add(c)
        }
        val vj = p.getString("vaults", "[]") ?: "[]"
        val varr = JSONArray(vj)
        for (i in 0 until varr.length()) {
            val o = varr.getJSONObject(i)
            val v = Vault(o.getString("id"), o.getString("name"), received = o.optBoolean("rec", false))
            val ia = o.optJSONArray("items") ?: JSONArray()
            for (j in 0 until ia.length()) {
                val io = ia.getJSONObject(j)
                v.items.add(VaultItem(io.getString("t"), io.getString("n"), io.getString("c")))
            }
            vaults.add(v)
        }
    }

    fun save() {
        val p = ctx.getSharedPreferences(PREFS, Context.MODE_PRIVATE)
        val carr = JSONArray()
        for (c in chans) {
            val o = JSONObject().put("id", c.id).put("name", c.name)
            val ma = JSONArray()
            for (m in c.messages) {
                ma.put(JSONObject().put("f", m.from).put("t", m.text).put("ts", m.ts))
            }
            o.put("msgs", ma)
            carr.put(o)
        }
        val varr = JSONArray()
        for (v in vaults) {
            val o = JSONObject().put("id", v.id).put("name", v.name).put("rec", v.received)
            val ia = JSONArray()
            for (i in v.items) {
                ia.put(JSONObject().put("t", i.type).put("n", i.name).put("c", i.content))
            }
            o.put("items", ia)
            varr.put(o)
        }
        p.edit().putString("chans", carr.toString()).putString("vaults", varr.toString()).apply()
    }

    fun findChan(id: String): Chan? = chans.firstOrNull { it.id == id }
    fun findVault(id: String): Vault? = vaults.firstOrNull { it.id == id }
    fun newId(): String = UUID.randomUUID().toString().replace("-", "").substring(0, 8)
}

// ============================================================
// MAIN ACTIVITY
// ============================================================
class MainActivity : Activity() {

    private var screen: String = "home"
    private var currentChanId: String? = null
    private var currentVaultId: String? = null
    private var pendingReplyChanId: String? = null
    private var pendingReplyChanName: String? = null
    private var pendingVaultIdForPick: String? = null

    private val REQ_PICK_IMAGE = 1001
    private val REQ_PICK_FILE = 1002

    private val BG = 0xFF0E1620.toInt()
    private val FG = 0xFFE8EEF5.toInt()
    private val ACCENT = 0xFF21D07A.toInt()
    private val MUTED = 0xFF8FA0B5.toInt()
    private val CARD = 0xFF17222E.toInt()
    private val DANGER = 0xFFE05252.toInt()

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        Store.init(this)
        handleIntent(intent)
        render()
    }

    override fun onNewIntent(intent: Intent?) {
        super.onNewIntent(intent)
        if (intent != null) {
            handleIntent(intent)
            render()
        }
    }

    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        if (resultCode != RESULT_OK) return
        val uri = data?.data ?: return
        val vaultId = pendingVaultIdForPick ?: return
        pendingVaultIdForPick = null
        val v = Store.findVault(vaultId) ?: return
        try {
            contentResolver.takePersistableUriPermission(
                uri, Intent.FLAG_GRANT_READ_URI_PERMISSION
            )
        } catch (e: Exception) { }
        val name = uri.lastPathSegment?.substringAfterLast('/')?.take(48) ?: "عنصر"
        val type = when (requestCode) {
            REQ_PICK_IMAGE -> "image"
            else -> "file"
        }
        v.items.add(VaultItem(type, name, uri.toString()))
        Store.save()
        currentVaultId = vaultId
        screen = "vault_view"
        render()
    }

    private fun handleIntent(intent: Intent) {
        val data: Uri = intent.data ?: return
        when (data.scheme) {
            "msgv1" -> handleMsgUri(data)
            "vaultv1" -> handleVaultUri(data)
        }
    }

    private fun handleMsgUri(uri: Uri) {
        val path = uri.pathSegments
        if (path.isEmpty()) return
        when (path[0]) {
            "chan" -> {
                if (path.size < 2) return
                val id = path[1]
                val name = uri.getQueryParameter("n") ?: "?"
                val own = Store.findChan(id)
                if (own != null) {
                    screen = "chan_inbox"; currentChanId = id
                } else {
                    pendingReplyChanId = id; pendingReplyChanName = name
                    screen = "write_reply"
                }
            }
            "msg" -> {
                if (path.size < 2) return
                val id = path[1]
                val from = uri.getQueryParameter("f") ?: "?"
                val msgB64 = uri.getQueryParameter("m") ?: return
                val msg = try {
                    String(Base64.decode(msgB64, Base64.URL_SAFE or Base64.NO_WRAP), Charsets.UTF_8)
                } catch (e: Exception) { return }
                val chan = Store.findChan(id)
                if (chan != null) {
                    chan.messages.add(MsgItem(from, msg, System.currentTimeMillis()))
                    Store.save()
                    Toast.makeText(this, "رسالة جديدة من $from", Toast.LENGTH_SHORT).show()
                    screen = "chan_inbox"; currentChanId = id
                } else {
                    Toast.makeText(this, "قناة غير معروفة: $id", Toast.LENGTH_LONG).show()
                }
            }
        }
    }

    private fun handleVaultUri(uri: Uri) {
        val path = uri.pathSegments
        if (path.isEmpty() || path[0] != "pack") return
        val name = uri.getQueryParameter("n") ?: "vault"
        val itemsB64 = uri.getQueryParameter("d") ?: return
        try {
            val json = String(Base64.decode(itemsB64, Base64.URL_SAFE or Base64.NO_WRAP), Charsets.UTF_8)
            val arr = JSONArray(json)
            val v = Vault(Store.newId(), name, received = true)
            for (i in 0 until arr.length()) {
                val o = arr.getJSONObject(i)
                v.items.add(VaultItem(o.getString("t"), o.getString("n"), o.getString("c")))
            }
            Store.vaults.add(v)
            Store.save()
            Toast.makeText(this, "تم استلام خزنة: $name", Toast.LENGTH_SHORT).show()
            screen = "vault_view"; currentVaultId = v.id
        } catch (e: Exception) {
            Toast.makeText(this, "بيانات خزنة تالفة", Toast.LENGTH_LONG).show()
        }
    }

    // ---------- UI builders ----------
    private fun dp(v: Int): Int = (v * resources.displayMetrics.density).toInt()

    private fun baseRoot(): LinearLayout {
        val root = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setBackgroundColor(BG)
            setPadding(dp(16), dp(20), dp(16), dp(12))
        }
        val title = TextView(this).apply {
            text = "QRX"
            setTextColor(ACCENT)
            textSize = 22f
            typeface = Typeface.DEFAULT_BOLD
            setPadding(0, 0, 0, dp(12))
        }
        root.addView(title)
        return root
    }

    private fun label(txt: String, color: Int = FG, size: Float = 14f): TextView =
        TextView(this).apply {
            text = txt; setTextColor(color); textSize = size
            setPadding(0, dp(4), 0, dp(4))
        }

    private fun btn(txt: String, onClick: () -> Unit): Button =
        Button(this).apply {
            text = txt
            setTextColor(BG)
            setBackgroundColor(ACCENT)
            setOnClickListener { onClick() }
            setPadding(dp(10), dp(6), dp(10), dp(6))
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            ).also { it.topMargin = dp(6); it.bottomMargin = dp(6) }
        }

    private fun btnSecondary(txt: String, onClick: () -> Unit): Button =
        Button(this).apply {
            text = txt
            setTextColor(FG)
            setBackgroundColor(CARD)
            setOnClickListener { onClick() }
            setPadding(dp(10), dp(6), dp(10), dp(6))
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            ).also { it.topMargin = dp(4); it.bottomMargin = dp(4) }
        }

    private fun input(hint: String, multi: Boolean = false): EditText =
        EditText(this).apply {
            this.hint = hint
            setTextColor(FG)
            setHintTextColor(MUTED)
            setBackgroundColor(CARD)
            setPadding(dp(10), dp(8), dp(10), dp(8))
            inputType = if (multi)
                InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_FLAG_MULTI_LINE
            else InputType.TYPE_CLASS_TEXT
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            ).also { it.topMargin = dp(4); it.bottomMargin = dp(4) }
        }

    private fun render() {
        val root = baseRoot()
        val scroll = ScrollView(this)
        val content = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL }
        scroll.addView(content)
        root.addView(scroll, LinearLayout.LayoutParams(
            ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f
        ))
        when (screen) {
            "home" -> buildHome(content)
            "messages" -> buildMessages(content)
            "create_chan" -> buildCreateChan(content)
            "chan_qr" -> buildChanQr(content)
            "chan_inbox" -> buildChanInbox(content)
            "write_reply" -> buildWriteReply(content)
            "vaults" -> buildVaults(content)
            "vault_view" -> buildVaultView(content)
            "vault_qr" -> buildVaultQr(content)
            else -> buildHome(content)
        }
        setContentView(root)
    }

    private fun buildHome(c: LinearLayout) {
        c.addView(label("القسم الأول — رسائل QR", ACCENT, 16f))
        c.addView(btn("فتح قسم الرسائل") { screen = "messages"; render() })
        c.addView(label("القسم الثاني — خزنة QR", ACCENT, 16f))
        c.addView(btn("فتح قسم الخزنة") { screen = "vaults"; render() })
    }

    private fun buildMessages(c: LinearLayout) {
        c.addView(btnSecondary("← رجوع") { screen = "home"; render() })
        c.addView(label("الفرع الأول — إنشاء باركود", ACCENT, 16f))
        c.addView(btn("إنشاء قناة جديدة") { screen = "create_chan"; render() })
        c.addView(label("الفرع الثاني — صندوق الرسائل", ACCENT, 16f))
        if (Store.chans.isEmpty()) {
            c.addView(label("لا توجد قنوات بعد.", MUTED))
        } else {
            for (ch in Store.chans) {
                val row = TextView(this).apply {
                    text = "${ch.name}  (${ch.messages.size})"
                    setTextColor(FG)
                    setBackgroundColor(CARD)
                    setPadding(dp(12), dp(10), dp(12), dp(10))
                    setOnClickListener {
                        currentChanId = ch.id
                        screen = "chan_inbox"
                        render()
                    }
                    layoutParams = LinearLayout.LayoutParams(
                        ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
                    ).also { it.topMargin = dp(4) }
                }
                c.addView(row)
            }
        }
        c.addView(btnSecondary("لصق باركود وارد (رد)") { showPasteDialog("msgv1") })
        c.addView(btnSecondary("لصق باركود وارد (خزنة)") { showPasteDialog("vaultv1") })
    }

    private fun buildCreateChan(c: LinearLayout) {
        c.addView(btnSecondary("← رجوع") { screen = "messages"; render() })
        c.addView(label("اسم القناة:"))
        val nameInput = input("مثال: أحمد")
        c.addView(nameInput)
        c.addView(btn("توليد الباركود") {
            val nm = nameInput.text.toString().trim()
            if (nm.isEmpty()) { toast("اكتب اسماً"); return@btn }
            val ch = Chan(Store.newId(), nm)
            Store.chans.add(ch)
            Store.save()
            currentChanId = ch.id
            screen = "chan_qr"
            render()
        })
    }

    private fun buildChanQr(c: LinearLayout) {
        val ch = Store.findChan(currentChanId ?: return) ?: return
        c.addView(btnSecondary("← رجوع") { screen = "chan_inbox"; render() })
        c.addView(label("شارك هذا الباركود: ${ch.name}", ACCENT))
        val payload = "msgv1://chan/${ch.id}?n=${Uri.encode(ch.name)}"
        val bmp = QrEncoder.renderBitmap(payload, 900)
        if (bmp == null) {
            c.addView(label("البيانات طويلة جداً — قصّر اسم القناة", DANGER))
            return
        }
        val iv = ImageView(this).apply {
            setImageBitmap(bmp)
            adjustViewBounds = true
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            ).also { it.topMargin = dp(8) }
        }
        c.addView(iv)
        c.addView(btnSecondary("نسخ نص الباركود") { copy(payload) })
        c.addView(btn("فتح صندوق الرسائل") { screen = "chan_inbox"; render() })
    }

    private fun buildChanInbox(c: LinearLayout) {
        val ch = Store.findChan(currentChanId ?: return) ?: return
        c.addView(btnSecondary("← رجوع") { screen = "messages"; render() })
        c.addView(label("صندوق: ${ch.name}", ACCENT, 16f))
        c.addView(btnSecondary("عرض باركود القناة") { screen = "chan_qr"; render() })
        if (ch.messages.isEmpty()) {
            c.addView(label("لا توجد رسائل بعد.", MUTED))
        } else {
            for (m in ch.messages.reversed()) {
                val v = TextView(this).apply {
                    text = "[${m.from}]\n${m.text}"
                    setTextColor(FG)
                    setBackgroundColor(CARD)
                    setPadding(dp(12), dp(10), dp(12), dp(10))
                    layoutParams = LinearLayout.LayoutParams(
                        ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
                    ).also { it.topMargin = dp(6) }
                }
                c.addView(v)
            }
        }
        c.addView(btnSecondary("لصق رد وارد") { showPasteDialog("msgv1") })
    }

    private fun buildWriteReply(c: LinearLayout) {
        val id = pendingReplyChanId ?: return
        val name = pendingReplyChanName ?: "?"
        c.addView(btnSecondary("← رجوع") { screen = "home"; render() })
        c.addView(label("إرسال رسالة إلى: $name", ACCENT, 16f))
        val fromInput = input("اسمك")
        val msgInput = input("نص الرسالة", multi = true)
        msgInput.minLines = 3
        msgInput.movementMethod = ScrollingMovementMethod()
        c.addView(fromInput); c.addView(msgInput)
        c.addView(btn("توليد باركود الرد") {
            val f = fromInput.text.toString().trim().ifEmpty { "?" }
            val m = msgInput.text.toString().trim()
            if (m.isEmpty()) { toast("اكتب رسالة"); return@btn }
            val b64 = Base64.encodeToString(m.toByteArray(Charsets.UTF_8), Base64.URL_SAFE or Base64.NO_WRAP)
            val uri = "msgv1://msg/$id?n=${Uri.encode(name)}&f=${Uri.encode(f)}&m=$b64"
            showQrDialog(uri, "أظهر هذا الباركود للمرسل")
        })
    }

    private fun buildVaults(c: LinearLayout) {
        c.addView(btnSecondary("← رجوع") { screen = "home"; render() })
        c.addView(btn("إنشاء خزنة جديدة") { createVaultDialog() })
        c.addView(btnSecondary("لصق باركود خزنة وارد") { showPasteDialog("vaultv1") })
        if (Store.vaults.isEmpty()) {
            c.addView(label("لا توجد خزائن بعد.", MUTED))
        } else {
            for (v in Store.vaults) {
                val tv = TextView(this).apply {
                    text = "${v.name}  (${v.items.size})${if (v.received) " • مستلمة" else ""}"
                    setTextColor(FG); setBackgroundColor(CARD)
                    setPadding(dp(12), dp(10), dp(12), dp(10))
                    setOnClickListener { currentVaultId = v.id; screen = "vault_view"; render() }
                    layoutParams = LinearLayout.LayoutParams(
                        ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
                    ).also { it.topMargin = dp(4) }
                }
                c.addView(tv)
            }
        }
    }

    private fun buildVaultView(c: LinearLayout) {
        val v = Store.findVault(currentVaultId ?: return) ?: return
        c.addView(btnSecondary("← رجوع") { screen = "vaults"; render() })
        c.addView(label("خزنة: ${v.name}", ACCENT, 16f))
        if (v.items.isEmpty()) c.addView(label("فارغة.", MUTED))
        for ((idx, item) in v.items.withIndex()) {
            val row = LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL
                setBackgroundColor(CARD)
                setPadding(dp(12), dp(8), dp(12), dp(8))
                layoutParams = LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
                ).also { it.topMargin = dp(4) }
            }
            val header = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL }
            when (item.type) {
                "image" -> {
                    val thumb = ImageView(this).apply {
                        setImageBitmap(loadThumbnail(Uri.parse(item.content), 96))
                        layoutParams = LinearLayout.LayoutParams(dp(64), dp(64))
                    }
                    header.addView(thumb)
                    val tv = TextView(this).apply {
                        text = "🖼 ${item.name}"
                        setTextColor(FG); setPadding(dp(8), 0, 0, 0)
                    }
                    header.addView(tv)
                }
                "app" -> {
                    val icon = ImageView(this).apply {
                        val pm = packageManager
                        try {
                            val info = pm.getApplicationInfo(item.content, 0)
                            setImageDrawable(pm.getApplicationIcon(info))
                        } catch (e: Exception) { }
                        layoutParams = LinearLayout.LayoutParams(dp(48), dp(48))
                    }
                    header.addView(icon)
                    val tv = TextView(this).apply {
                        text = "📱 ${item.name}"
                        setTextColor(FG); setPadding(dp(8), 0, 0, 0)
                    }
                    header.addView(tv)
                }
                "file" -> {
                    val tv = TextView(this).apply {
                        text = "📎 ${item.name}"
                        setTextColor(FG)
                    }
                    header.addView(tv)
                }
                else -> {
                    val tv = TextView(this).apply {
                        text = "📝 ${item.name}"
                        setTextColor(FG)
                    }
                    header.addView(tv)
                }
            }
            row.addView(header)
            if (item.type == "text") {
                val body = TextView(this).apply {
                    text = item.content.take(300)
                    setTextColor(MUTED)
                    setPadding(0, dp(4), 0, 0)
                }
                row.addView(body)
            }
            row.setOnClickListener { openItem(item) }
            row.setOnLongClickListener {
                AlertDialog.Builder(this@MainActivity)
                    .setMessage("حذف ${item.name}؟")
                    .setPositiveButton("حذف") { _, _ ->
                        v.items.removeAt(idx); Store.save(); render()
                    }
                    .setNegativeButton("إلغاء", null).show()
                true
            }
            c.addView(row)
        }
        if (!v.received) {
            c.addView(label("إضافة عناصر:", MUTED, 12f))
            c.addView(btn("➕ إضافة صورة من الجهاز") { pickFromDevice(REQ_PICK_IMAGE, "image/*", v.id) })
            c.addView(btnSecondary("➕ إضافة ملف من الجهاز") { pickFromDevice(REQ_PICK_FILE, "*/*", v.id) })
            c.addView(btnSecondary("➕ إضافة تطبيق مثبت") { showAppPicker(v) })
            c.addView(btn("إضافة نص") { addTextToVault(v) })
            c.addView(label("ملاحظة: الصور والملفات تُشارك كمرجع محلي (URI) صالح على نفس الجهاز فقط.", MUTED, 11f))
            c.addView(btn("توليد باركود الخزنة") {
                val payload = packVault(v)
                if (payload == null) { toast("الخزنة كبيرة جداً للباركود"); return@btn }
                currentVaultId = v.id
                screen = "vault_qr"
                render()
                showQrDialog(payload, "شارك هذا الباركود — سيستلمه الشخص كخزنة")
            })
        }
    }

    private fun buildVaultQr(c: LinearLayout) {
        val v = Store.findVault(currentVaultId ?: return) ?: return
        c.addView(btnSecondary("← رجوع") { screen = "vault_view"; render() })
        val payload = packVault(v)
        if (payload == null) {
            c.addView(label("الخزنة كبيرة جداً للباركود — قلل العناصر", DANGER))
            return
        }
        c.addView(label("باركود خزنة: ${v.name}", ACCENT))
        val bmp = QrEncoder.renderBitmap(payload, 900)
        if (bmp == null) {
            c.addView(label("البيانات طويلة جداً", DANGER))
            return
        }
        val iv = ImageView(this).apply {
            setImageBitmap(bmp); adjustViewBounds = true
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            ).also { it.topMargin = dp(8) }
        }
        c.addView(iv)
        c.addView(btnSecondary("نسخ نص الباركود") { copy(payload) })
    }

    private fun pickFromDevice(req: Int, mime: String, vaultId: String) {
        pendingVaultIdForPick = vaultId
        val intent = Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
            addCategory(Intent.CATEGORY_OPENABLE)
            type = mime
            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
        }
        try { startActivityForResult(intent, req) }
        catch (e: Exception) { toast("لا يوجد تطبيق لاختيار الملفات") }
    }

    private fun showAppPicker(v: Vault) {
        val pm = packageManager
        val apps = pm.getInstalledApplications(0)
            .filter { pm.getLaunchIntentForPackage(it.packageName) != null }
            .sortedBy { pm.getApplicationLabel(it).toString() }
        if (apps.isEmpty()) { toast("لا توجد تطبيقات"); return }
        val names = apps.map { pm.getApplicationLabel(it).toString() }.toTypedArray()
        AlertDialog.Builder(this)
            .setTitle("اختر تطبيقاً")
            .setItems(names) { _, idx ->
                val info = apps[idx]
                val label = pm.getApplicationLabel(info).toString()
                v.items.add(VaultItem("app", label, info.packageName))
                Store.save()
                currentVaultId = v.id
                screen = "vault_view"
                render()
            }
            .setNegativeButton("إلغاء", null).show()
    }

    private fun openItem(item: VaultItem) {
        when (item.type) {
            "image", "file" -> {
                try {
                    val uri = Uri.parse(item.content)
                    val intent = Intent(Intent.ACTION_VIEW).apply {
                        setDataAndType(uri, contentResolver.getType(uri) ?: "*/*")
                        addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
                    }
                    startActivity(intent)
                } catch (e: Exception) {
                    toast("لا يمكن فتح العنصر (قد يكون من جهاز آخر)")
                }
            }
            "app" -> {
                val intent = packageManager.getLaunchIntentForPackage(item.content)
                if (intent != null) try { startActivity(intent) }
                catch (e: Exception) { toast("غير متاح على هذا الجهاز") }
                else toast("التطبيق غير مثبت")
            }
            "text" -> {
                AlertDialog.Builder(this)
                    .setTitle(item.name)
                    .setMessage(item.content)
                    .setPositiveButton("إغلاق", null).show()
            }
        }
    }

    private fun loadThumbnail(uri: Uri, maxPx: Int): Bitmap? {
        return try {
            val opts = BitmapFactory.Options().apply { inJustDecodeBounds = true }
            contentResolver.openInputStream(uri)?.use { BitmapFactory.decodeStream(it, null, opts) }
            val longest = maxOf(opts.outWidth, opts.outHeight).coerceAtLeast(1)
            var sample = 1
            while (longest / sample > maxPx) sample *= 2
            val opts2 = BitmapFactory.Options().apply { inSampleSize = sample }
            contentResolver.openInputStream(uri)?.use { BitmapFactory.decodeStream(it, null, opts2) }
        } catch (e: Exception) { null }
    }

    private fun createVaultDialog() {
        val et = EditText(this).apply {
            hint = "اسم الخزنة"; setTextColor(FG); setHintTextColor(MUTED)
            setBackgroundColor(CARD); setPadding(dp(10), dp(8), dp(10), dp(8))
        }
        AlertDialog.Builder(this)
            .setTitle("خزنة جديدة")
            .setView(et)
            .setPositiveButton("إنشاء") { _, _ ->
                val nm = et.text.toString().trim().ifEmpty { "خزنة" }
                val v = Vault(Store.newId(), nm)
                Store.vaults.add(v); Store.save()
                currentVaultId = v.id; screen = "vault_view"; render()
            }
            .setNegativeButton("إلغاء", null).show()
    }

    private fun addTextToVault(v: Vault) {
        val nameEt = EditText(this).apply {
            hint = "العنوان"; setTextColor(FG); setHintTextColor(MUTED)
            setBackgroundColor(CARD); setPadding(dp(10), dp(8), dp(10), dp(8))
        }
        val contentEt = EditText(this).apply {
            hint = "المحتوى"; setTextColor(FG); setHintTextColor(MUTED)
            setBackgroundColor(CARD); setPadding(dp(10), dp(8), dp(10), dp(8))
            inputType = InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_FLAG_MULTI_LINE
            minLines = 3
        }
        val layout = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(dp(20), dp(10), dp(20), dp(10))
            addView(nameEt); addView(contentEt)
        }
        AlertDialog.Builder(this)
            .setTitle("نص جديد")
            .setView(layout)
            .setPositiveButton("إضافة") { _, _ ->
                val n = nameEt.text.toString().trim().ifEmpty { "نص" }
                val c = contentEt.text.toString()
                v.items.add(VaultItem("text", n, c))
                Store.save(); render()
            }
            .setNegativeButton("إلغاء", null).show()
    }

    private fun packVault(v: Vault): String? {
        val arr = JSONArray()
        for (item in v.items) {
            arr.put(JSONObject().put("t", item.type).put("n", item.name).put("c", item.content))
        }
        val json = arr.toString()
        val b64 = Base64.encodeToString(json.toByteArray(Charsets.UTF_8), Base64.URL_SAFE or Base64.NO_WRAP)
        val uri = "vaultv1://pack/${v.id}?n=${Uri.encode(v.name)}&d=$b64"
        if (uri.toByteArray(Charsets.UTF_8).size > 170) {
            return null
        }
        return uri
    }

    private fun showQrDialog(payload: String, hint: String) {
        val bmp = QrEncoder.renderBitmap(payload, 900)
        if (bmp == null) { toast("البيانات طويلة جداً للباركود"); return }
        val iv = ImageView(this).apply {
            setImageBitmap(bmp); adjustViewBounds = true
        }
        val tv = TextView(this).apply {
            text = hint; setTextColor(FG); setPadding(dp(8), dp(8), dp(8), dp(8))
            gravity = Gravity.CENTER
        }
        val box = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(dp(16), dp(16), dp(16), dp(16))
            addView(tv); addView(iv)
        }
        AlertDialog.Builder(this)
            .setView(box)
            .setPositiveButton("نسخ النص") { _, _ -> copy(payload) }
            .setNegativeButton("إغلاق", null).show()
    }

    private fun showPasteDialog(scheme: String) {
        val et = EditText(this).apply {
            hint = "$scheme://..."
            setTextColor(FG); setHintTextColor(MUTED); setBackgroundColor(CARD)
            setPadding(dp(10), dp(8), dp(10), dp(8))
            inputType = InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_FLAG_MULTI_LINE
            minLines = 3
        }
        val box = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(dp(16), dp(16), dp(16), dp(16))
            addView(label("الصق نص الباركود المستلم:", FG))
            addView(et)
        }
        AlertDialog.Builder(this)
            .setTitle("باركود وارد")
            .setView(box)
            .setPositiveButton("معالجة") { _, _ ->
                val txt = et.text.toString().trim()
                if (txt.isEmpty()) return@setPositiveButton
                val uri = Uri.parse(txt)
                when (uri.scheme) {
                    "msgv1" -> handleMsgUri(uri)
                    "vaultv1" -> handleVaultUri(uri)
                    else -> toast("مخطط URI غير معروف")
                }
                render()
            }
            .setNegativeButton("إلغاء", null).show()
    }

    private fun copy(text: String) {
        val cm = getSystemService(Context.CLIPBOARD_SERVICE) as android.content.ClipboardManager
        cm.setPrimaryClip(android.content.ClipData.newPlainText("qr", text))
        toast("تم النسخ")
    }

    private fun toast(msg: String) {
        Toast.makeText(this, msg, Toast.LENGTH_SHORT).show()
    }
}