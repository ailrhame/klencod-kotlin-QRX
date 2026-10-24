package com.qrx.ncr

import android.app.Activity
import android.app.AlertDialog
import android.app.Notification
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.Service
import android.content.Context
import android.content.Intent
import android.content.pm.PackageManager
import android.content.pm.ServiceInfo
import android.graphics.Bitmap
import android.graphics.BitmapFactory
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.Typeface
import android.net.Uri
import android.os.Build
import android.os.Bundle
import android.os.IBinder
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
import java.io.ByteArrayOutputStream
import java.io.OutputStream
import java.net.Inet4Address
import java.net.NetworkInterface
import java.net.ServerSocket
import java.net.Socket
import java.net.URLDecoder
import java.util.Collections
import java.util.UUID

// ============================================================
// QR ENCODER — byte mode, versions 1-9, error correction level M
// ============================================================
object QrEncoder {
    private val ECC_M = intArrayOf(10, 16, 26, 18, 24, 16, 18, 22, 22)
    private val BLOCKS_M = intArrayOf(1, 1, 1, 2, 2, 4, 4, 4, 5)
    private val FORMAT_M = intArrayOf(0x5412, 0x5125, 0x5E7C, 0x5B4B, 0x45F9, 0x40CE, 0x4F97, 0x4AA0)
    private val VERSION_INFO = intArrayOf(0, 0, 0, 0, 0, 0, 0x07C94, 0x085BC, 0x09A99)

    private val GF_EXP = IntArray(512)
    private val GF_LOG = IntArray(256)
    init {
        var x = 1
        for (i in 0 until 255) {
            GF_EXP[i] = x; GF_LOG[x] = i
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
        val r = IntArray(deg); r[deg - 1] = 1
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
        appendBits(bits, 4, 4); appendBits(bits, bytes.size, 8)
        for (b in bytes) appendBits(bits, b.toInt() and 0xFF, 8)
        val cap = dataCodewords(ver) * 8
        repeat(minOf(4, cap - bits.size)) { bits.add(false) }
        while (bits.size % 8 != 0) bits.add(false)
        var pad = true
        while (bits.size < cap) {
            appendBits(bits, if (pad) 0xEC else 0x11, 8); pad = !pad
        }
        return bits
    }

    private fun bitsToCodewords(bits: List<Boolean>, ver: Int): IntArray {
        val n = dataCodewords(ver); val cw = IntArray(n)
        for (i in 0 until n) {
            var b = 0
            for (j in 0 until 8) if (bits[i * 8 + j]) b = b or (1 shl (7 - j))
            cw[i] = b
        }
        return cw
    }

    private fun interleave(data: IntArray, ver: Int): IntArray {
        val numBlocks = BLOCKS_M[ver - 1]; val eccLen = ECC_M[ver - 1]
        val total = data.size; val shortSize = total / numBlocks; val numLong = total % numBlocks
        val dataBlocks = mutableListOf<IntArray>(); val eccBlocks = mutableListOf<IntArray>()
        var pos = 0
        for (i in 0 until numBlocks) {
            val size = shortSize + if (i >= numBlocks - numLong) 1 else 0
            val block = IntArray(size); System.arraycopy(data, pos, block, 0, size); pos += size
            dataBlocks.add(block); eccBlocks.add(rsEncode(block, eccLen))
        }
        val out = mutableListOf<Int>()
        val maxData = shortSize + if (numLong > 0) 1 else 0
        for (i in 0 until maxData) for (b in dataBlocks) if (i < b.size) out.add(b[i])
        for (i in 0 until eccLen) for (e in eccBlocks) out.add(e[i])
        return out.toIntArray()
    }

    private fun alignmentPositions(ver: Int): IntArray = when (ver) {
        1 -> intArrayOf(); 2 -> intArrayOf(6, 18); 3 -> intArrayOf(6, 22)
        4 -> intArrayOf(6, 26); 5 -> intArrayOf(6, 30); 6 -> intArrayOf(6, 34)
        7 -> intArrayOf(6, 22, 38); 8 -> intArrayOf(6, 24, 42); 9 -> intArrayOf(6, 26, 46)
        else -> intArrayOf()
    }

    private fun placeFinder(m: Array<BooleanArray>, res: Array<BooleanArray>, row: Int, col: Int) {
        for (dr in -1..7) for (dc in -1..7) {
            val rr = row + dr; val cc = col + dc
            if (rr < 0 || rr >= m.size || cc < 0 || cc >= m.size) continue
            res[rr][cc] = true
            val border = dr == 0 || dr == 6 || dc == 0 || dc == 6
            val inner = dr in 2..4 && dc in 2..4
            if (border || inner) m[rr][cc] = true
        }
    }

    private fun placeAlignment(m: Array<BooleanArray>, res: Array<BooleanArray>, row: Int, col: Int) {
        for (dr in 0..4) for (dc in 0..4) {
            res[row + dr][col + dc] = true
            val border = dr == 0 || dr == 4 || dc == 0 || dc == 4
            val center = dr == 2 && dc == 2
            if (border || center) m[row + dr][col + dc] = true
        }
    }

    private fun placeVersionInfo(m: Array<BooleanArray>, res: Array<BooleanArray>, ver: Int) {
        if (ver < 7) return
        val v = VERSION_INFO[ver - 1]; val size = m.size
        for (i in 0 until 18) {
            val bit = ((v shr i) and 1) == 1
            m[i / 3][size - 11 + (i % 3)] = bit; res[i / 3][size - 11 + (i % 3)] = true
            m[size - 11 + (i % 3)][i / 3] = bit; res[size - 11 + (i % 3)][i / 3] = true
        }
    }

    private fun placeMatrix(cw: IntArray, ver: Int): Pair<Array<BooleanArray>, Array<BooleanArray>> {
        val size = 17 + 4 * ver
        val m = Array(size) { BooleanArray(size) }
        val res = Array(size) { BooleanArray(size) }
        placeFinder(m, res, 0, 0); placeFinder(m, res, 0, size - 7); placeFinder(m, res, size - 7, 0)
        val aps = alignmentPositions(ver)
        for (r in aps) for (c in aps) {
            if ((r == 6 && c == 6) || (r == 6 && c == size - 7) || (r == size - 7 && c == 6)) continue
            placeAlignment(m, res, r - 2, c - 2)
        }
        for (i in 8 until size - 8) {
            m[6][i] = i % 2 == 0; res[6][i] = true
            m[i][6] = i % 2 == 0; res[i][6] = true
        }
        m[size - 8][8] = true; res[size - 8][8] = true
        for (i in 0 until 9) { res[8][i] = true; res[i][8] = true }
        for (i in 0 until 8) { res[8][size - 1 - i] = true; res[size - 1 - i][8] = true }
        placeVersionInfo(m, res, ver)
        var bit = 0; var col = size - 1; var up = true
        while (col > 0) {
            if (col == 6) col--
            for (row in 0 until size) {
                val r = if (up) size - 1 - row else row
                for (k in 0..1) {
                    val c = col - k
                    if (res[r][c]) continue
                    if (bit < cw.size * 8) {
                        m[r][c] = ((cw[bit / 8] shr (7 - (bit % 8))) and 1) == 1
                        bit++
                    }
                }
            }
            up = !up; col -= 2
        }
        return Pair(m, res)
    }

    private fun applyMask(m: Array<BooleanArray>, res: Array<BooleanArray>, mask: Int) {
        for (r in m.indices) for (c in m.indices) {
            if (res[r][c]) continue
            val inv = when (mask) { 0 -> (r + c) % 2 == 0; else -> false }
            if (inv) m[r][c] = !m[r][c]
        }
    }

    private fun bitOf(x: Int, i: Int) = ((x shr i) and 1) == 1

    private fun placeFormat(m: Array<BooleanArray>, mask: Int) {
        val f = FORMAT_M[mask]; val s = m.size
        m[8][0] = bitOf(f, 14); m[8][1] = bitOf(f, 13); m[8][2] = bitOf(f, 12)
        m[8][3] = bitOf(f, 11); m[8][4] = bitOf(f, 10); m[8][5] = bitOf(f, 9)
        m[8][7] = bitOf(f, 8); m[8][8] = bitOf(f, 7); m[7][8] = bitOf(f, 6)
        m[5][8] = bitOf(f, 5); m[4][8] = bitOf(f, 4); m[3][8] = bitOf(f, 3)
        m[2][8] = bitOf(f, 2); m[1][8] = bitOf(f, 1); m[0][8] = bitOf(f, 0)
        m[s - 1][8] = bitOf(f, 14); m[s - 2][8] = bitOf(f, 13); m[s - 3][8] = bitOf(f, 12)
        m[s - 4][8] = bitOf(f, 11); m[s - 5][8] = bitOf(f, 10); m[s - 6][8] = bitOf(f, 9)
        m[s - 7][8] = bitOf(f, 8)
        m[8][s - 8] = bitOf(f, 7); m[8][s - 7] = bitOf(f, 6); m[8][s - 6] = bitOf(f, 5)
        m[8][s - 5] = bitOf(f, 4); m[8][s - 4] = bitOf(f, 3); m[8][s - 3] = bitOf(f, 2)
        m[8][s - 2] = bitOf(f, 1); m[8][s - 1] = bitOf(f, 0)
    }

    fun renderBitmap(text: String, sizePx: Int): Bitmap? {
        val bytes = text.toByteArray(Charsets.UTF_8)
        val ver = try { chooseVersion(bytes.size) } catch (e: Exception) { return null }
        val bits = encodeData(bytes, ver)
        val cw = bitsToCodewords(bits, ver)
        val all = interleave(cw, ver)
        val (m, res) = placeMatrix(all, ver)
        applyMask(m, res, 0); placeFormat(m, 0)

        val modules = m.size; val quiet = 4; val total = modules + quiet * 2
        val scale = (sizePx / total).coerceAtLeast(1); val bmpSize = total * scale
        val bmp = Bitmap.createBitmap(bmpSize, bmpSize, Bitmap.Config.ARGB_8888)
        val canvas = Canvas(bmp); canvas.drawColor(Color.WHITE)
        val black = Paint().apply { color = Color.BLACK; isAntiAlias = false }
        for (r in 0 until modules) for (c in 0 until modules) {
            if (m[r][c]) {
                val x = (c + quiet) * scale; val y = (r + quiet) * scale
                canvas.drawRect(x.toFloat(), y.toFloat(), (x + scale).toFloat(), (y + scale).toFloat(), black)
            }
        }
        return bmp
    }
}

// ============================================================
// MODELS
// ============================================================
data class MsgItem(val from: String, val text: String, val ts: Long)
data class Chan(val id: String, val name: String, val messages: MutableList<MsgItem> = mutableListOf())
data class VaultItem(val type: String, val name: String, val content: String)
data class Vault(val id: String, val name: String, val items: MutableList<VaultItem> = mutableListOf())

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

    fun appCtx(): Context = ctx

    fun load() {
        val p = ctx.getSharedPreferences(PREFS, Context.MODE_PRIVATE)
        chans.clear(); vaults.clear()
        val carr = JSONArray(p.getString("chans", "[]") ?: "[]")
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
        val varr = JSONArray(p.getString("vaults", "[]") ?: "[]")
        for (i in 0 until varr.length()) {
            val o = varr.getJSONObject(i)
            val v = Vault(o.getString("id"), o.getString("name"))
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
            for (m in c.messages) ma.put(JSONObject().put("f", m.from).put("t", m.text).put("ts", m.ts))
            o.put("msgs", ma); carr.put(o)
        }
        val varr = JSONArray()
        for (v in vaults) {
            val o = JSONObject().put("id", v.id).put("name", v.name)
            val ia = JSONArray()
            for (i in v.items) ia.put(JSONObject().put("t", i.type).put("n", i.name).put("c", i.content))
            o.put("items", ia); varr.put(o)
        }
        p.edit().putString("chans", carr.toString()).putString("vaults", varr.toString()).apply()
    }

    fun findChan(id: String): Chan? = chans.firstOrNull { it.id == id }
    fun findVault(id: String): Vault? = vaults.firstOrNull { it.id == id }
    fun newId(): String = UUID.randomUUID().toString().replace("-", "").substring(0, 8)
}

// ============================================================
// LAN SERVER — Premium Embedded UI
// ============================================================
object LanServer {
    private var serverSocket: ServerSocket? = null
    private var thread: Thread? = null
    private lateinit var ctx: Context
    @Volatile var port: Int = 0; private set
    @Volatile private var running = false

    fun start(appContext: Context) {
        if (running) return
        ctx = appContext
        val prefs = ctx.getSharedPreferences("qrx_server", Context.MODE_PRIVATE)
        val last = prefs.getInt("port", 8080)
        val candidates = mutableListOf(last)
        for (p in 8080..8090) if (p != last) candidates.add(p)
        var s: ServerSocket? = null
        for (p in candidates) {
            try { s = ServerSocket(p); port = p; break } catch (e: Exception) { }
        }
        if (s == null) return
        prefs.edit().putInt("port", port).apply()
        serverSocket = s
        running = true
        thread = Thread {
            while (running) {
                try {
                    val client = s.accept()
                    Thread { handleClient(client) }.start()
                } catch (e: Exception) { if (!running) break }
            }
        }.also { it.isDaemon = true; it.start() }
    }

    fun stop() {
        running = false
        try { serverSocket?.close() } catch (e: Exception) { }
        serverSocket = null
    }

    fun lanIp(): String? {
        try {
            val ifaces = Collections.list(NetworkInterface.getNetworkInterfaces())
                .filter { it.isUp && !it.isLoopback }
                .sortedByDescending { it.name.startsWith("wlan") }
            for (iface in ifaces) {
                for (addr in Collections.list(iface.inetAddresses)) {
                    if (addr is Inet4Address && !addr.isLoopbackAddress) return addr.hostAddress
                }
            }
        } catch (e: Exception) { }
        return null
    }

    private fun handleClient(socket: Socket) {
        try {
            socket.use { sock ->
                sock.soTimeout = 15000
                val inp = sock.getInputStream()
                val hbuf = ByteArrayOutputStream()
                val ring = IntArray(4)
                while (true) {
                    val b = inp.read()
                    if (b < 0) break
                    hbuf.write(b)
                    ring[0] = ring[1]; ring[1] = ring[2]; ring[2] = ring[3]; ring[3] = b
                    if (ring[0] == '\r'.code && ring[1] == '\n'.code &&
                        ring[2] == '\r'.code && ring[3] == '\n'.code) break
                    if (hbuf.size() > 8192) break
                }
                val headerText = hbuf.toString("UTF-8")
                var contentLen = 0
                for (line in headerText.split("\r\n")) {
                    if (line.startsWith("Content-Length:", ignoreCase = true)) {
                        contentLen = line.substringAfter(":").trim().toIntOrNull() ?: 0
                    }
                }
                val bodySb = StringBuilder()
                if (contentLen > 0) {
                    val raw = ByteArray(contentLen); var got = 0
                    while (got < contentLen) {
                        val r = inp.read(raw, got, contentLen - got)
                        if (r <= 0) break
                        got += r
                    }
                    bodySb.append(String(raw, 0, got, Charsets.UTF_8))
                }
                val line1 = headerText.substringBefore("\r\n")
                val parts = line1.split(" ")
                if (parts.size < 2) return
                val method = parts[0]
                val fullPath = parts[1]
                val path = fullPath.substringBefore('?')
                val qs = fullPath.substringAfter('?', "")
                route(sock.getOutputStream(), method, path, qs, bodySb.toString())
            }
        } catch (e: Exception) { }
    }

    private fun route(out: OutputStream, method: String, path: String, qs: String, body: String) {
        val seg = path.trimStart('/').split('/').filter { it.isNotEmpty() }
        try {
            when {
                seg.size == 2 && seg[0] == "c" && method == "GET" -> {
                    val name = try {
                        Uri.parse("http://x/?$qs").getQueryParameter("n")
                    } catch (e: Exception) { null } ?: "?"
                    sendHtml(out, composePage(seg[1], name))
                }
                seg.size == 2 && seg[0] == "s" && method == "POST" -> {
                    val params = parseForm(body)
                    val from = params["f"]?.trim().orEmpty().ifEmpty { "مجهول" }
                    val msg = params["m"]?.trim().orEmpty()
                    val ch = Store.findChan(seg[1])
                    if (ch != null && msg.isNotEmpty()) {
                        ch.messages.add(MsgItem(from, msg, System.currentTimeMillis()))
                        Store.save()
                    }
                    sendHtml(out, thanksPage(from))
                }
                seg.size == 4 && seg[0] == "v" && seg[2] == "raw" && method == "GET" -> {
                    val v = Store.findVault(seg[1])
                    val idx = seg[3].toIntOrNull()
                    val item = if (v != null && idx != null) v.items.getOrNull(idx) else null
                    if (item == null) send404(out) else serveBytes(out, item)
                }
                seg.size == 2 && seg[0] == "v" && method == "GET" -> {
                    val v = Store.findVault(seg[1])
                    if (v == null) send404(out) else sendHtml(out, vaultPage(v))
                }
                else -> send404(out)
            }
        } catch (e: Exception) {
            try { send500(out) } catch (x: Exception) { }
        }
    }

    private fun parseForm(body: String): Map<String, String> {
        val m = mutableMapOf<String, String>()
        for (pair in body.split("&")) {
            val i = pair.indexOf('='); if (i < 0) continue
            val k = URLDecoder.decode(pair.substring(0, i), "UTF-8")
            val v = URLDecoder.decode(pair.substring(i + 1), "UTF-8")
            m[k] = v
        }
        return m
    }

    private fun sendHtml(out: OutputStream, html: String) {
        val b = html.toByteArray(Charsets.UTF_8)
        val h = "HTTP/1.0 200 OK\r\nContent-Type: text/html; charset=utf-8\r\nContent-Length: ${b.size}\r\nConnection: close\r\n\r\n"
        out.write(h.toByteArray(Charsets.UTF_8)); out.write(b); out.flush()
    }

    private fun send404(out: OutputStream) {
        val b = "<!DOCTYPE html><html><body style='background:#0a0a0d;color:#fff;text-align:center;padding:40px;font-family:sans-serif'><h1>404</h1><p>غير موجود</p></body></html>".toByteArray(Charsets.UTF_8)
        val h = "HTTP/1.0 404 Not Found\r\nContent-Type: text/html; charset=utf-8\r\nContent-Length: ${b.size}\r\nConnection: close\r\n\r\n"
        out.write(h.toByteArray(Charsets.UTF_8)); out.write(b); out.flush()
    }

    private fun send500(out: OutputStream) {
        val b = "<h1>500</h1>".toByteArray(Charsets.UTF_8)
        out.write("HTTP/1.0 500\r\nContent-Type: text/html\r\nContent-Length: ${b.size}\r\nConnection: close\r\n\r\n".toByteArray()); out.write(b); out.flush()
    }

    private fun serveBytes(out: OutputStream, item: VaultItem) {
        try {
            val uri = Uri.parse(item.content)
            val input = ctx.contentResolver.openInputStream(uri)
            if (input == null) { send404(out); return }
            val mime = ctx.contentResolver.getType(uri) ?: "application/octet-stream"
            val safeName = item.name.replace("\"", "").replace("\n", " ")
            out.write(("HTTP/1.0 200 OK\r\nContent-Type: $mime\r\nContent-Disposition: inline; filename=\"$safeName\"\r\nConnection: close\r\n\r\n").toByteArray(Charsets.UTF_8))
            val buf = ByteArray(64 * 1024); var n: Int
            while (input.read(buf).also { n = it } > 0) out.write(buf, 0, n)
            input.close(); out.flush()
        } catch (e: Exception) { try { send404(out) } catch (x: Exception) { } }
    }

    private fun esc(s: String): String = s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace("\"", "&quot;")

    // ------------------------------------------------------------
    // PREMIUM MESSAGE UI
    // ------------------------------------------------------------
    private fun composePage(chanId: String, name: String): String {
        val safe = esc(name)
        val initial = if (name.isNotEmpty()) name.substring(0, 1).uppercase() else "A"
        return """<!DOCTYPE html>
<html dir="rtl" lang="ar"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="theme-color" content="#0a0a0d">
<title>$safe — إرسال رسالة</title>
<style>
  :root { --accent: #a855f7; --bg: #0a0a0d; --panel: #16171b; --line: #2a2d34; --text: #e8e9ee; --muted: #8a8f9c; }
  * { box-sizing: border-box; -webkit-tap-highlight-color: transparent; }
  body { margin: 0; background: radial-gradient(circle at 50% 15%, #1c1c22 0%, var(--bg) 70%); color: var(--text); font-family: system-ui, -apple-system, sans-serif; padding-bottom: 40px; }
  .topbar { display: flex; align-items: center; justify-content: space-between; padding: 12px 16px; background: rgba(15,15,15,0.8); backdrop-filter: blur(10px); border-bottom: 1px solid var(--line); position: sticky; top: 0; z-index: 10; }
  .logo { display: flex; align-items: center; gap: 8px; font-weight: 800; font-size: 16px; letter-spacing: -0.5px; }
  .logo span { color: #ff0000; font-size: 20px; }
  .chline { display: flex; align-items: center; gap: 14px; padding: 20px 16px; border-bottom: 1px solid var(--line); }
  .av { width: 52px; height: 52px; border-radius: 50%; background: linear-gradient(135deg, var(--accent), #7c3aed); display: flex; align-items: center; justify-content: center; font-weight: 800; font-size: 24px; flex-shrink: 0; box-shadow: 0 4px 12px rgba(168,85,247,0.3); }
  .chname { font-weight: 700; font-size: 17px; }
  .subs { font-size: 12px; color: var(--muted); margin-top: 3px; }
  .subbtn { background: var(--accent); color: #fff; border: none; padding: 8px 18px; border-radius: 20px; font-weight: 700; font-size: 13px; margin-right: auto; box-shadow: 0 4px 14px rgba(168,85,247,0.4); }
  .video-placeholder { position: relative; width: 100%; padding-bottom: 56.25%; background: linear-gradient(45deg, #101114, #1a1b22); display: flex; align-items: center; justify-content: center; border-bottom: 1px solid var(--line); }
  .play-icon { position: absolute; width: 60px; height: 60px; background: rgba(168,85,247,0.2); border: 2px solid var(--accent); border-radius: 50%; display: flex; align-items: center; justify-content: center; font-size: 24px; color: var(--accent); animation: pulse 2s infinite; }
  @keyframes pulse { 0% { box-shadow: 0 0 0 0 rgba(168,85,247,0.5); } 70% { box-shadow: 0 0 0 20px rgba(168,85,247,0); } 100% { box-shadow: 0 0 0 0 rgba(168,85,247,0); } }
  .meta { padding: 16px; }
  .title { font-weight: 700; font-size: 16px; margin-bottom: 6px; line-height: 1.4; }
  .metasmall { font-size: 12px; color: var(--muted); }
  .divider { height: 1px; background: var(--line); margin: 0 16px; }
  .comments { padding: 20px 16px; }
  .form { display: flex; flex-direction: column; gap: 16px; }
  .row { display: flex; gap: 12px; align-items: center; }
  .row input { flex: 1; background: var(--panel); border: 1px solid var(--line); border-radius: 12px; padding: 14px; color: var(--text); font-size: 14px; outline: none; font-family: inherit; transition: 0.2s; }
  .row input:focus { border-color: var(--accent); box-shadow: 0 0 0 3px rgba(168,85,247,0.15); }
  .row input::placeholder { color: var(--muted); }
  button { background: linear-gradient(180deg, var(--accent), #7c3aed); color: #fff; border: none; border-radius: 12px; padding: 14px 24px; font-weight: 700; font-size: 15px; cursor: pointer; font-family: inherit; box-shadow: 0 4px 15px rgba(168,85,247,0.4); transition: 0.1s; }
  button:active { transform: scale(0.97); }
  .hint { color: var(--muted); font-size: 11px; text-align: center; padding: 30px 16px; line-height: 1.8; }
</style></head><body>
<div class="topbar"><div class="logo"><span>▶</span> YouTube</div></div>
<div class="chline">
  <div class="av">$initial</div>
  <div><div class="chname">$safe</div><div class="subs">قناة QRX • تفاعل مباشر</div></div>
  <button class="subbtn" type="button">مشترك ✓</button>
</div>
<div class="video-placeholder"><div class="play-icon">▶</div></div>
<div class="meta">
  <div class="title">أرسل رسالة إلى $safe</div>
  <div class="metasmall">ستُسلَّم فوراً إلى تطبيق QRX على جهاز صاحب القناة</div>
</div>
<div class="divider"></div>
<div class="comments">
  <form class="form" method="POST" action="/s/$chanId">
    <div class="row">
      <input type="text" name="f" placeholder="اسمك (اختياري)" maxlength="40">
    </div>
    <div class="row">
      <input type="text" name="m" placeholder="اكتب تعليقاً..." required maxlength="400" autofocus>
    </div>
    <div class="row" style="justify-content:flex-end">
      <button type="submit">إرسال</button>
    </div>
  </form>
</div>
<div class="hint">📶 يجب أن تكون على نفس شبكة WiFi<br>أبقِ تطبيق QRX مفتوحاً على جهاز المستقبل</div>
</body></html>"""
    }

    private fun thanksPage(from: String): String {
        val safe = esc(from)
        return """<!DOCTYPE html>
<html dir="rtl"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>تم الإرسال</title>
<style>
  body { margin: 0; background: radial-gradient(circle at 50% 15%, #1c1c22 0%, #0a0a0d 70%); color: #e8e9ee; font-family: system-ui, sans-serif; display: flex; align-items: center; justify-content: center; min-height: 100vh; padding: 24px; }
  .box { background: linear-gradient(155deg, #16171b, #101114); border: 1px solid rgba(168,85,247,0.3); border-radius: 20px; padding: 40px 24px; max-width: 400px; width: 100%; text-align: center; box-shadow: 0 20px 50px rgba(0,0,0,0.7), 0 0 40px rgba(168,85,247,0.1); animation: popIn 0.5s cubic-bezier(0.175, 0.885, 0.32, 1.275); }
  @keyframes popIn { from { transform: scale(0.8); opacity: 0; } to { transform: scale(1); opacity: 1; } }
  .ic { font-size: 64px; margin-bottom: 16px; text-shadow: 0 0 20px rgba(110,247,166,0.5); }
  h1 { font-size: 22px; margin: 0 0 12px; color: #6ef7a6; }
  p { color: #8a8f9c; font-size: 14px; line-height: 1.6; margin: 0; }
  .sign { margin-top: 20px; color: #a855f7; font-size: 13px; font-weight: 700; }
</style></head><body>
<div class="box">
  <div class="ic">✅</div>
  <h1>تم الإرسال بنجاح</h1>
  <p>وصلت رسالتك إلى تطبيق QRX على جهاز صاحب القناة.</p>
  <p class="sign">— $safe</p>
</div>
</body></html>"""
    }

    // ------------------------------------------------------------
    // PREMIUM VAULT UI
    // ------------------------------------------------------------
    private fun vaultPage(v: Vault): String {
        val sb = StringBuilder()
        for ((idx, item) in v.items.withIndex()) {
            sb.append("<div class=\"card\">")
            when (item.type) {
                "image" -> {
                    sb.append("<div class=\"tag t-img\">📷 صورة</div>")
                    sb.append("<h3>${esc(item.name)}</h3>")
                    sb.append("<img src=\"/v/${v.id}/raw/$idx\" alt=\"\">")
                }
                "file" -> {
                    sb.append("<div class=\"tag t-file\">📎 ملف</div>")
                    sb.append("<h3>${esc(item.name)}</h3>")
                    sb.append("<a href=\"/v/${v.id}/raw/$idx\" download>⬇ تنزيل الملف</a>")
                }
                "app" -> {
                    sb.append("<div class=\"tag t-app\">📱 تطبيق</div>")
                    sb.append("<h3>${esc(item.name)}</h3>")
                    sb.append("<div class=\"body\">الحزمة: <code>${esc(item.content)}</code></div>")
                }
                else -> {
                    sb.append("<div class=\"tag t-text\">📝 نص</div>")
                    sb.append("<h3>${esc(item.name)}</h3>")
                    sb.append("<div class=\"body\">${esc(item.content)}</div>")
                }
            }
            sb.append("</div>")
        }
        val safe = esc(v.name)
        return """<!DOCTYPE html>
<html dir="rtl" lang="ar"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="theme-color" content="#0a0a0d">
<title>خزنة $safe</title>
<style>
  :root { --accent: #a855f7; --bg: #0a0a0d; --panel: #101114; --panel-2: #16171b; --line: #2a2d34; --text: #e8e9ee; --muted: #8a8f9c; --ok: #6ef7a6; }
  * { box-sizing: border-box; -webkit-tap-highlight-color: transparent; }
  body { margin: 0; background: radial-gradient(circle at 50% 15%, #1c1c22 0%, var(--bg) 70%); color: var(--text); font-family: system-ui, sans-serif; padding: 20px 16px 60px; min-height: 100vh; }
  .header { text-align: center; margin-bottom: 30px; animation: fadeInDown 0.6s ease; }
  @keyframes fadeInDown { from { transform: translateY(-20px); opacity: 0; } to { transform: translateY(0); opacity: 1; } }
  .header h1 { font-size: 24px; margin: 0 0 8px; font-weight: 800; }
  .header h1 span { color: var(--accent); }
  .header .count { color: var(--muted); font-size: 13px; background: rgba(168,85,247,0.1); display: inline-block; padding: 4px 12px; border-radius: 20px; border: 1px solid rgba(168,85,247,0.2); }
  .grid { display: flex; flex-direction: column; gap: 16px; max-width: 600px; margin: 0 auto; }
  .card { background: linear-gradient(155deg, var(--panel-2), var(--panel)); border: 1px solid var(--line); border-radius: 16px; padding: 16px; box-shadow: 0 10px 30px rgba(0,0,0,0.5); overflow: hidden; animation: slideUp 0.4s ease both; }
  .card:nth-child(1) { animation-delay: 0.1s; } .card:nth-child(2) { animation-delay: 0.15s; } .card:nth-child(3) { animation-delay: 0.2s; }
  @keyframes slideUp { from { transform: translateY(20px); opacity: 0; } to { transform: translateY(0); opacity: 1; } }
  .card h3 { margin: 8px 0 10px; font-size: 16px; font-weight: 700; word-break: break-word; }
  .tag { display: inline-block; font-size: 11px; font-weight: 800; padding: 4px 10px; border-radius: 8px; letter-spacing: 0.5px; }
  .t-img { background: rgba(255, 85, 85, 0.15); color: #ff7a7a; border: 1px solid rgba(255, 85, 85, 0.3); }
  .t-file { background: rgba(85, 170, 255, 0.15); color: #7af; border: 1px solid rgba(85, 170, 255, 0.3); }
  .t-app { background: rgba(170, 85, 255, 0.15); color: #c7f; border: 1px solid rgba(170, 85, 255, 0.3); }
  .t-text { background: rgba(255, 255, 85, 0.15); color: #ee7; border: 1px solid rgba(255, 255, 85, 0.3); }
  .body { color: #c7cad2; white-space: pre-wrap; word-break: break-word; font-size: 14px; line-height: 1.6; }
  .card img { width: 100%; border-radius: 12px; display: block; margin-top: 10px; background: #000; box-shadow: 0 4px 15px rgba(0,0,0,0.4); }
  .card a { display: inline-block; color: var(--accent); text-decoration: none; font-weight: 700; padding: 10px 16px; background: rgba(168,85,247,0.1); border: 1px solid rgba(168,85,247,0.3); border-radius: 10px; font-size: 14px; margin-top: 6px; transition: 0.2s; }
  .card a:hover { background: rgba(168,85,247,0.2); }
  code { background: #000; padding: 3px 8px; border-radius: 6px; font-size: 12px; color: #7ff; font-family: monospace; }
  .footer { color: #555; font-size: 11px; text-align: center; padding: 30px 16px; line-height: 1.8; }
</style></head><body>
<div class="header">
  <h1>🔒 خزنة <span>$safe</span></h1>
  <div class="count">${v.items.size} عنصر</div>
</div>
<div class="grid">
$sb
</div>
<div class="footer">📶 المحتوى يُبث مباشرة من جهاز صاحب الخزنة<br>يجب أن تكون على نفس شبكة WiFi</div>
</body></html>"""
    }
}

// ============================================================
// FOREGROUND SERVICE
// ============================================================
class QrxService : Service() {
    override fun onBind(intent: Intent?): IBinder? = null

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        val chId = "qrx_server"
        val nm = getSystemService(NotificationManager::class.java)
        if (Build.VERSION.SDK_INT >= 26) {
            nm.createNotificationChannel(
                NotificationChannel(chId, "QRX Server", NotificationManager.IMPORTANCE_LOW)
            )
        }
        val notif: Notification = if (Build.VERSION.SDK_INT >= 26) {
            Notification.Builder(this, chId)
        } else {
            @Suppress("DEPRECATION") Notification.Builder(this)
        }
            .setContentTitle("QRX يعمل")
            .setContentText("في انتظار الرسائل على الشبكة المحلية")
            .setSmallIcon(android.R.drawable.ic_menu_view)
            .setOngoing(true)
            .build()

        try {
            if (Build.VERSION.SDK_INT >= 34) {
                startForeground(42, notif, ServiceInfo.FOREGROUND_SERVICE_TYPE_SPECIAL_USE)
            } else {
                startForeground(42, notif)
            }
        } catch (e: Exception) { }

        LanServer.start(applicationContext)
        return START_STICKY
    }

    override fun onDestroy() {
        LanServer.stop()
        super.onDestroy()
    }
}

// ============================================================
// MAIN ACTIVITY
// ============================================================
class MainActivity : Activity() {
    private var screen: String = "home"
    private var currentChanId: String? = null
    private var currentVaultId: String? = null
    private var pendingVaultIdForPick: String? = null

    private val REQ_PICK_IMAGE = 1001
    private val REQ_PICK_FILE = 1002
    private val REQ_NOTIF = 2001

    private val BG = 0xFF0E1620.toInt()
    private val FG = 0xFFE8EEF5.toInt()
    private val ACCENT = 0xFF21D07A.toInt()
    private val MUTED = 0xFF8FA0B5.toInt()
    private val CARD = 0xFF17222E.toInt()
    private val DANGER = 0xFFE05252.toInt()

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        Store.init(this)
        requestNotifPerm()
        val si = Intent(this, QrxService::class.java)
        try {
            if (Build.VERSION.SDK_INT >= 26) startForegroundService(si) else startService(si)
        } catch (e: Exception) { }
        render()
    }

    private fun requestNotifPerm() {
        if (Build.VERSION.SDK_INT >= 33) {
            if (checkSelfPermission("android.permission.POST_NOTIFICATIONS") != PackageManager.PERMISSION_GRANTED) {
                requestPermissions(arrayOf("android.permission.POST_NOTIFICATIONS"), REQ_NOTIF)
            }
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
            contentResolver.takePersistableUriPermission(uri, Intent.FLAG_GRANT_READ_URI_PERMISSION)
        } catch (e: Exception) { }
        val name = uri.lastPathSegment?.substringAfterLast('/')?.take(60) ?: "عنصر"
        val type = if (requestCode == REQ_PICK_IMAGE) "image" else "file"
        v.items.add(VaultItem(type, name, uri.toString()))
        Store.save()
        currentVaultId = vaultId
        screen = "vault_view"
        render()
    }

    private fun dp(v: Int): Int = (v * resources.displayMetrics.density).toInt()

    private fun baseRoot(): LinearLayout {
        val root = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setBackgroundColor(BG)
            setPadding(dp(16), dp(20), dp(16), dp(12))
        }
        val title = TextView(this).apply {
            text = "QRX"
            setTextColor(ACCENT); textSize = 22f
            typeface = Typeface.DEFAULT_BOLD
            setPadding(0, 0, 0, dp(12))
        }
        root.addView(title)
        return root
    }

    private fun label(t: String, color: Int = FG, size: Float = 14f): TextView =
        TextView(this).apply {
            text = t; setTextColor(color); textSize = size
            setPadding(0, dp(4), 0, dp(4))
        }

    private fun btn(t: String, onClick: () -> Unit): Button =
        Button(this).apply {
            text = t; setTextColor(BG); setBackgroundColor(ACCENT)
            setOnClickListener { onClick() }
            setPadding(dp(10), dp(6), dp(10), dp(6))
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            ).also { it.topMargin = dp(6); it.bottomMargin = dp(6) }
        }

    private fun btnSecondary(t: String, onClick: () -> Unit): Button =
        Button(this).apply {
            text = t; setTextColor(FG); setBackgroundColor(CARD)
            setOnClickListener { onClick() }
            setPadding(dp(10), dp(6), dp(10), dp(6))
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            ).also { it.topMargin = dp(4); it.bottomMargin = dp(4) }
        }

    private fun input(hint: String, multi: Boolean = false): EditText =
        EditText(this).apply {
            this.hint = hint; setTextColor(FG); setHintTextColor(MUTED); setBackgroundColor(CARD)
            setPadding(dp(10), dp(8), dp(10), dp(8))
            inputType = if (multi) InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_FLAG_MULTI_LINE
            else InputType.TYPE_CLASS_TEXT
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            ).also { it.topMargin = dp(4); it.bottomMargin = dp(4) }
        }

    private fun serverBase(): String? {
        val ip = LanServer.lanIp() ?: return null
        if (LanServer.port == 0) return null
        return "http://$ip:${LanServer.port}"
    }

    private fun render() {
        val root = baseRoot()
        val scroll = ScrollView(this)
        val content = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL }
        scroll.addView(content)
        root.addView(scroll, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f))
        when (screen) {
            "home" -> buildHome(content)
            "messages" -> buildMessages(content)
            "create_chan" -> buildCreateChan(content)
            "chan_qr" -> buildChanQr(content)
            "chan_inbox" -> buildChanInbox(content)
            "vaults" -> buildVaults(content)
            "vault_view" -> buildVaultView(content)
            "vault_qr" -> buildVaultQr(content)
            else -> buildHome(content)
        }
        setContentView(root)
    }

    private fun buildHome(c: LinearLayout) {
        val base = serverBase()
        if (base == null) {
            c.addView(label("⚠ لا اتصال WiFi أو الخادم لم يبدأ بعد.", DANGER, 12f))
            c.addView(label("اتصل بشبكة WiFi وأعد المحاولة.", MUTED, 11f))
        } else {
            c.addView(label("📶 الخادم يعمل: ${LanServer.lanIp()}:${LanServer.port}", MUTED, 11f))
        }
        c.addView(label("القسم الأول — رسائل QR", ACCENT, 16f))
        c.addView(btn("فتح قسم الرسائل") { screen = "messages"; render() })
        c.addView(label("القسم الثاني — خزنة QR", ACCENT, 16f))
        c.addView(btn("فتح قسم الخزنة") { screen = "vaults"; render() })
    }

    private fun buildMessages(c: LinearLayout) {
        c.addView(btnSecondary("← رجوع") { screen = "home"; render() })
        c.addView(label("الفرع الأول — إنشاء قناة", ACCENT, 16f))
        c.addView(btn("إنشاء قناة جديدة") { screen = "create_chan"; render() })
        c.addView(label("الفرع الثاني — صندوق الرسائل", ACCENT, 16f))
        if (Store.chans.isEmpty()) {
            c.addView(label("لا توجد قنوات بعد.", MUTED))
        } else {
            for (ch in Store.chans) {
                val row = TextView(this).apply {
                    text = "${ch.name}  (${ch.messages.size})"
                    setTextColor(FG); setBackgroundColor(CARD)
                    setPadding(dp(12), dp(10), dp(12), dp(10))
                    setOnClickListener { currentChanId = ch.id; screen = "chan_inbox"; render() }
                    layoutParams = LinearLayout.LayoutParams(
                        ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
                    ).also { it.topMargin = dp(4) }
                }
                c.addView(row)
            }
        }
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
            Store.chans.add(ch); Store.save()
            currentChanId = ch.id; screen = "chan_qr"; render()
        })
    }

    private fun buildChanQr(c: LinearLayout) {
        val ch = Store.findChan(currentChanId ?: return) ?: return
        c.addView(btnSecondary("← رجوع") { screen = "chan_inbox"; render() })
        val base = serverBase()
        if (base == null) {
            c.addView(label("⚠ لا شبكة WiFi أو الخادم لم يبدأ — أعد تشغيل التطبيق على WiFi.", DANGER))
            return
        }
        val url = "$base/c/${ch.id}?n=${Uri.encode(ch.name)}"
        c.addView(label("امسح الباركود بأي كاميرا:", ACCENT))
        val bmp = QrEncoder.renderBitmap(url, 900)
        if (bmp == null) { c.addView(label("البيانات طويلة جداً", DANGER)); return }
        c.addView(ImageView(this).apply {
            setImageBitmap(bmp); adjustViewBounds = true
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            ).also { it.topMargin = dp(8) }
        })
        c.addView(label(url, MUTED, 10f))
        c.addView(btn("فتح صندوق الرسائل") { screen = "chan_inbox"; render() })
        c.addView(label("⚠ يجب أن يكون الماسح على نفس شبكة WiFi.", MUTED, 11f))
    }

    private fun buildChanInbox(c: LinearLayout) {
        val ch = Store.findChan(currentChanId ?: return) ?: return
        c.addView(btnSecondary("← رجوع") { screen = "messages"; render() })
        c.addView(label("صندوق: ${ch.name}", ACCENT, 16f))
        c.addView(btnSecondary("عرض باركود القناة") { screen = "chan_qr"; render() })
        if (ch.messages.isEmpty()) {
            c.addView(label("لا توجد رسائل بعد — بانتظار وصولها...", MUTED))
        } else {
            for (m in ch.messages.reversed()) {
                val v = TextView(this).apply {
                    text = "[${m.from}]\n${m.text}"
                    setTextColor(FG); setBackgroundColor(CARD)
                    setPadding(dp(12), dp(10), dp(12), dp(10))
                    layoutParams = LinearLayout.LayoutParams(
                        ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
                    ).also { it.topMargin = dp(6) }
                }
                c.addView(v)
            }
        }
        c.addView(btnSecondary("تحديث") { render() })
    }

    private fun buildVaults(c: LinearLayout) {
        c.addView(btnSecondary("← رجوع") { screen = "home"; render() })
        c.addView(btn("إنشاء خزنة جديدة") { createVaultDialog() })
        if (Store.vaults.isEmpty()) {
            c.addView(label("لا توجد خزائن بعد.", MUTED))
        } else {
            for (v in Store.vaults) {
                val tv = TextView(this).apply {
                    text = "${v.name}  (${v.items.size})"
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
                orientation = LinearLayout.VERTICAL; setBackgroundColor(CARD)
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
                    header.addView(TextView(this).apply {
                        text = "🖼 ${item.name}"; setTextColor(FG); setPadding(dp(8), 0, 0, 0)
                    })
                }
                "app" -> {
                    val icon = ImageView(this).apply {
                        try {
                            val info = packageManager.getApplicationInfo(item.content, 0)
                            setImageDrawable(packageManager.getApplicationIcon(info))
                        } catch (e: Exception) { }
                        layoutParams = LinearLayout.LayoutParams(dp(48), dp(48))
                    }
                    header.addView(icon)
                    header.addView(TextView(this).apply {
                        text = "📱 ${item.name}"; setTextColor(FG); setPadding(dp(8), 0, 0, 0)
                    })
                }
                "file" -> header.addView(TextView(this).apply { text = "📎 ${item.name}"; setTextColor(FG) })
                else -> header.addView(TextView(this).apply { text = "📝 ${item.name}"; setTextColor(FG) })
            }
            row.addView(header)
            if (item.type == "text") row.addView(TextView(this).apply {
                text = item.content.take(300); setTextColor(MUTED); setPadding(0, dp(4), 0, 0)
            })
            row.setOnLongClickListener {
                AlertDialog.Builder(this@MainActivity)
                    .setMessage("حذف ${item.name}؟")
                    .setPositiveButton("حذف") { _, _ -> v.items.removeAt(idx); Store.save(); render() }
                    .setNegativeButton("إلغاء", null).show()
                true
            }
            c.addView(row)
        }
        c.addView(label("إضافة عناصر:", MUTED, 12f))
        c.addView(btn("➕ صورة من الجهاز") { pickFromDevice(REQ_PICK_IMAGE, "image/*", v.id) })
        c.addView(btnSecondary("➕ ملف من الجهاز") { pickFromDevice(REQ_PICK_FILE, "*/*", v.id) })
        c.addView(btnSecondary("➕ تطبيق مثبت") { showAppPicker(v) })
        c.addView(btn("إضافة نص") { addTextToVault(v) })
        c.addView(btn("توليد باركود الخزنة") {
            screen = "vault_qr"; render()
        })
    }

    private fun buildVaultQr(c: LinearLayout) {
        val v = Store.findVault(currentVaultId ?: return) ?: return
        c.addView(btnSecondary("← رجوع") { screen = "vault_view"; render() })
        val base = serverBase()
        if (base == null) {
            c.addView(label("⚠ لا شبكة WiFi أو الخادم لم يبدأ.", DANGER)); return
        }
        if (v.items.isEmpty()) { c.addView(label("أضف عناصر أولاً.", DANGER)); return }
        val url = "$base/v/${v.id}"
        c.addView(label("امسح الباركود — ستظهر الصور والملفات مباشرة:", ACCENT))
        val bmp = QrEncoder.renderBitmap(url, 900)
        if (bmp == null) { c.addView(label("البيانات طويلة جداً", DANGER)); return }
        c.addView(ImageView(this).apply {
            setImageBitmap(bmp); adjustViewBounds = true
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            ).also { it.topMargin = dp(8) }
        })
        c.addView(label(url, MUTED, 10f))
        c.addView(label("⚠ يجب أن يكون الماسح على نفس شبكة WiFi.", MUTED, 11f))
    }

    private fun pickFromDevice(req: Int, mime: String, vaultId: String) {
        pendingVaultIdForPick = vaultId
        val intent = Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
            addCategory(Intent.CATEGORY_OPENABLE); type = mime
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
        AlertDialog.Builder(this).setTitle("اختر تطبيقاً")
            .setItems(names) { _, idx ->
                val info = apps[idx]
                val label = pm.getApplicationLabel(info).toString()
                v.items.add(VaultItem("app", label, info.packageName))
                Store.save(); currentVaultId = v.id; screen = "vault_view"; render()
            }
            .setNegativeButton("إلغاء", null).show()
    }

    private fun loadThumbnail(uri: Uri, maxPx: Int): Bitmap? {
        return try {
            val opts = BitmapFactory.Options().apply { inJustDecodeBounds = true }
            contentResolver.openInputStream(uri)?.use { BitmapFactory.decodeStream(it, null, opts) }
            val longest = maxOf(opts.outWidth, opts.outHeight).coerceAtLeast(1)
            var s = 1; while (longest / s > maxPx) s *= 2
            val o2 = BitmapFactory.Options().apply { inSampleSize = s }
            contentResolver.openInputStream(uri)?.use { BitmapFactory.decodeStream(it, null, o2) }
        } catch (e: Exception) { null }
    }

    private fun createVaultDialog() {
        val et = EditText(this).apply {
            hint = "اسم الخزنة"; setTextColor(FG); setHintTextColor(MUTED)
            setBackgroundColor(CARD); setPadding(dp(10), dp(8), dp(10), dp(8))
        }
        AlertDialog.Builder(this).setTitle("خزنة جديدة").setView(et)
            .setPositiveButton("إنشاء") { _, _ ->
                val nm = et.text.toString().trim().ifEmpty { "خزنة" }
                val v = Vault(Store.newId(), nm)
                Store.vaults.add(v); Store.save()
                currentVaultId = v.id; screen = "vault_view"; render()
            }.setNegativeButton("إلغاء", null).show()
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
        AlertDialog.Builder(this).setTitle("نص جديد").setView(layout)
            .setPositiveButton("إضافة") { _, _ ->
                val n = nameEt.text.toString().trim().ifEmpty { "نص" }
                v.items.add(VaultItem("text", n, contentEt.text.toString()))
                Store.save(); render()
            }.setNegativeButton("إلغاء", null).show()
    }

    private fun toast(msg: String) {
        Toast.makeText(this, msg, Toast.LENGTH_SHORT).show()
    }
}