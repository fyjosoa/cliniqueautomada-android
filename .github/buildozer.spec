[app]
title = Clinique Auto Mada
package.name = cliniqueautomada
package.domain = mg.cliniqueautomada
source.dir = .
source.include_exts = py
version = 13.0
requirements = python3,kivy==2.3.0,reportlab,pillow,androidstorage4kivy,pypdf
orientation = portrait
fullscreen = 0

# INTERNET : e-mail / IA optionnelle. Lecture du stockage : import PDF/Word.
android.permissions = INTERNET,READ_EXTERNAL_STORAGE
android.api = 34
android.minapi = 24
android.archs = arm64-v8a, armeabi-v7a
android.accept_sdk_license = True

[buildozer]
log_level = 2
warn_on_root = 0
