# QRX

مشروع Android Kotlin أُنشئ بـ KlencodIDE.

## القالب: لوحة رسم بسيطة 🎨

### الميزات
- رسم بالإصبع (Canvas + Path)
- 8 ألوان + 3 سماكات فرشاة
- تراجع (Undo) + مسح الكل
- حفظ PNG في Pictures/KlencodDrawings (Android 10+)
- كل المنطق في ملف MainActivity.kt واحد
- لا مكتبات خارجية (فقط kotlin-stdlib)

### البناء

يتم البناء تلقائياً على GitHub Actions عند الضغط على "بناء APK" من داخل التطبيق.

### الهيكل
- `app/src/main/java/` — كود Kotlin (MainActivity.kt فقط)
- `app/src/main/res/` — الموارد (strings.xml + app_icon.png)
- `app/src/main/AndroidManifest.xml` — بيان التطبيق
- `app/module.toml` — إعدادات الوحدة

### التوسيعات المقترحة
- 🧹 ممحاة (Eraser)
- ↪️ إعادة (Redo)
- 📤 مشاركة الصورة
- 🎨 منتقي ألوان HSL
- 🌐 شبكة خلفية

### Kotlin idiom

هذا القالب يستخدم:
- `data class` للـ Stroke
- `when` بدل `switch`
- `?.` و `?:` لـ Null safety
- `mutableListOf` بدل `ArrayList`
- Top-level functions داخل `object`
