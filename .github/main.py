# -*- coding: utf-8 -*-
"""
CliniqueAutoMada V13 - PERFORMANCE (base V12 : devis réutilisables) (IA autonome, contrôle intelligent) + import multiple PDF/Word et archive (V9.10.6)

Dépendances : kivy, reportlab (+ pillow)
Android (buildozer.spec) :
    requirements = python3,kivy,reportlab,pillow,androidstorage4kivy
    android.permissions = INTERNET
"""

import bisect
import calendar
import csv
import difflib
import functools
import json
import glob
import mimetypes
import os
import re
import smtplib
import ssl
import socket
import sqlite3
import threading
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
import hashlib
import zipfile
import xml.etree.ElementTree as ET
from contextlib import contextmanager
from datetime import datetime, timedelta
from email.message import EmailMessage

import statistics

from kivy.app import App
from kivy.clock import Clock
from kivy.core.window import Window
from kivy.metrics import dp, sp
from kivy.uix.boxlayout import BoxLayout
from kivy.uix.filechooser import FileChooserListView
from kivy.uix.button import Button
from kivy.uix.gridlayout import GridLayout
from kivy.uix.label import Label
from kivy.uix.popup import Popup
from kivy.uix.screenmanager import ScreenManager, Screen
from kivy.uix.scrollview import ScrollView
from kivy.uix.spinner import Spinner
from kivy.uix.textinput import TextInput
from kivy.utils import platform

try:
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.utils import simpleSplit
    from reportlab.pdfbase.pdfmetrics import stringWidth
    from reportlab.pdfgen import canvas
    HAS_REPORTLAB = True
except ImportError:
    HAS_REPORTLAB = False

# Sur Android, le clavier virtuel ne doit pas cacher le champ en cours de saisie
Window.softinput_mode = "below_target"


# ============================================================
# CHEMINS (calculés au démarrage : ~ n'est pas fiable sur Android)
# ============================================================

DOSSIER_APP = DOSSIER_PDF = DOSSIER_SAUV = DB_PATH = ""


def init_chemins(app):
    global DOSSIER_APP, DOSSIER_PDF, DOSSIER_SAUV, DB_PATH
    if platform == "android":
        DOSSIER_APP = app.user_data_dir
    else:  # même dossier qu'avant : vos données existantes sont conservées
        DOSSIER_APP = os.path.join(os.path.expanduser("~"), "CliniqueAutoMada")
    DOSSIER_PDF = os.path.join(DOSSIER_APP, "PDF_Export")
    DOSSIER_SAUV = os.path.join(DOSSIER_APP, "Sauvegardes")
    os.makedirs(DOSSIER_PDF, exist_ok=True)
    os.makedirs(DOSSIER_SAUV, exist_ok=True)
    DB_PATH = os.path.join(DOSSIER_APP, "clinique_auto_mada.db")


# ============================================================
# COULEURS
# ============================================================

BLEU = (0.20, 0.58, 0.88, 1)
BLEU_FONCE = (0.07, 0.28, 0.52, 1)
GRIS_TEXTE = (0.3, 0.3, 0.3, 1)
GRIS = (0.5, 0.5, 0.5, 1)
VERT = (0.15, 0.65, 0.35, 1)
ROUGE = (0.72, 0.16, 0.16, 1)
ORANGE = (0.92, 0.52, 0.15, 1)


# ============================================================
# BASE DE DONNÉES
# ============================================================

_WAL_ACTIF = False


def _activer_wal():
    """Mode WAL : lectures et écritures ne se bloquent plus (recherche en arrière-plan).
    Réglage persistant dans le fichier ; s'il échoue, la base reste en mode classique."""
    global _WAL_ACTIF
    try:
        conn = sqlite3.connect(DB_PATH, timeout=30)
        try:
            _WAL_ACTIF = str(conn.execute("PRAGMA journal_mode=WAL").fetchone()[0]).lower() == "wal"
        finally:
            conn.close()
    except sqlite3.Error:
        _WAL_ACTIF = False


@contextmanager
def db():
    """Connexion avec commit/rollback automatiques et fermeture garantie."""
    conn = sqlite3.connect(DB_PATH, timeout=30)
    conn.row_factory = sqlite3.Row
    try:  # fonctions « deterministic » : SQLite peut réutiliser les résultats (Python >= 3.8)
        conn.create_function("norm", 1, normaliser, deterministic=True)      # minuscules, sans accents
        conn.create_function("compact", 1, compacter, deterministic=True)    # + sans espaces ni tirets
    except (TypeError, sqlite3.NotSupportedError):
        conn.create_function("norm", 1, normaliser)
        conn.create_function("compact", 1, compacter)
    if _WAL_ACTIF:
        conn.execute("PRAGMA synchronous=NORMAL")    # sûr en WAL : pas de corruption possible
    conn.execute("PRAGMA temp_store=MEMORY")
    conn.execute("PRAGMA cache_size=-8000")          # ~8 Mo de cache par connexion
    try:
        yield conn
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


SCHEMA_VERSION = 4  # V9.10.4+ : archivage des documents PDF/Word extraits


def sauvegarder_base(motif="manuelle", garder=15):
    """Sauvegarde SQLite compatible Python 3.8 / Windows 7 / Android.

    Retourne le chemin de la sauvegarde si elle est valide, sinon None.
    La base active n'est jamais copiée directement au niveau du fichier.
    """
    if not DB_PATH or not os.path.isfile(DB_PATH):
        return None

    try:
        garder = max(1, int(garder))
    except (TypeError, ValueError):
        garder = 15

    src = dst = None
    temporaire = None
    dest = None

    try:
        os.makedirs(DOSSIER_SAUV, exist_ok=True)

        # Empêche les caractères problématiques dans le nom du fichier.
        motif = re.sub(r"[^A-Za-z0-9_-]", "_", str(motif)) or "manuelle"
        horodatage = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
        dest = os.path.join(DOSSIER_SAUV, "base_{}_{}.db".format(motif, horodatage))
        temporaire = dest + ".tmp"

        # Ouvrir directement la base : db() est un context manager, pas une connexion.
        src = sqlite3.connect(DB_PATH, timeout=30)
        dst = sqlite3.connect(temporaire, timeout=30)
        src.backup(dst)
        dst.commit()
        dst.close()
        dst = None
        src.close()
        src = None

        # Vérifier la sauvegarde avant de la publier.
        controle = sqlite3.connect(temporaire, timeout=30)
        try:
            resultat = controle.execute("PRAGMA quick_check").fetchone()
            if not resultat or resultat[0] != "ok":
                raise sqlite3.DatabaseError("Le contrôle d'intégrité de la sauvegarde a échoué.")
        finally:
            controle.close()

        # Le fichier temporaire est dans le même dossier, donc remplacement local.
        os.replace(temporaire, dest)
        temporaire = None

        # Ne supprimer les anciennes sauvegardes qu'après réussite de la nouvelle.
        anciennes = sorted(
            glob.glob(os.path.join(DOSSIER_SAUV, "base_*.db")),
            key=os.path.getmtime,
            reverse=True
        )
        for ancien in anciennes[garder:]:
            if ancien != dest:
                try:
                    os.remove(ancien)
                except OSError:
                    pass

        return dest

    except Exception as erreur:
        print("Erreur sauvegarde CliniqueAutoMada : {}".format(erreur))
        return None

    finally:
        if dst is not None:
            try:
                dst.close()
            except Exception:
                pass
        if src is not None:
            try:
                src.close()
            except Exception:
                pass
        if temporaire and os.path.exists(temporaire):
            try:
                os.remove(temporaire)
            except OSError:
                pass


def sauvegarde_du_jour():
    if not glob.glob(os.path.join(DOSSIER_SAUV, f"base_auto_{datetime.now():%Y%m%d}_*.db")):
        sauvegarder_base("auto")


def verifier_integrite():
    with db() as c:
        return c.execute("PRAGMA integrity_check").fetchone()[0] == "ok"


def _ajouter_colonnes(cur, table, colonnes):
    existantes = {r[1] for r in cur.execute(f"PRAGMA table_info({table})")}
    for nom, definition in colonnes:
        if nom not in existantes:
            cur.execute(f"ALTER TABLE {table} ADD COLUMN {nom} {definition}")


def init_database():
    if os.path.exists(DB_PATH):
        with db() as c:
            ancienne = c.execute("PRAGMA user_version").fetchone()[0]
        if ancienne < SCHEMA_VERSION:  # filet de sécurité avant de toucher à vos données
            sauvegarder_base(f"avant_migration_v{ancienne}")
    _activer_wal()
    with db() as c:
        c.execute("""CREATE TABLE IF NOT EXISTS clients (
            id INTEGER PRIMARY KEY AUTOINCREMENT, nom TEXT DEFAULT '',
            telephone TEXT DEFAULT '', adresse TEXT DEFAULT '')""")
        c.execute("""CREATE TABLE IF NOT EXISTS vehicules (
            id INTEGER PRIMARY KEY AUTOINCREMENT, client_id INTEGER,
            marque TEXT DEFAULT '', modele TEXT DEFAULT '',
            immatriculation TEXT DEFAULT '', kilometrage TEXT DEFAULT '',
            moteur TEXT DEFAULT '', vin TEXT DEFAULT '')""")
        c.execute("""CREATE TABLE IF NOT EXISTS devis (
            id INTEGER PRIMARY KEY AUTOINCREMENT, client TEXT DEFAULT '',
            vehicule TEXT DEFAULT '', immatriculation TEXT DEFAULT '',
            date_devis TEXT DEFAULT '', kilometrage TEXT DEFAULT '',
            total REAL DEFAULT 0, statut TEXT DEFAULT 'En attente')""")
        c.execute("""CREATE TABLE IF NOT EXISTS lignes_devis (
            id INTEGER PRIMARY KEY AUTOINCREMENT, devis_id INTEGER, numero INTEGER,
            type_ligne TEXT DEFAULT 'Pièce', designation TEXT DEFAULT '',
            quantite REAL DEFAULT 1, prix_unitaire REAL DEFAULT 0, total REAL DEFAULT 0)""")
        c.execute("""CREATE TABLE IF NOT EXISTS factures (
            id INTEGER PRIMARY KEY AUTOINCREMENT, devis_id INTEGER,
            client TEXT DEFAULT '', vehicule TEXT DEFAULT '',
            immatriculation TEXT DEFAULT '', date_facture TEXT DEFAULT '',
            total REAL DEFAULT 0)""")
        c.execute("""CREATE TABLE IF NOT EXISTS lignes_facture (
            id INTEGER PRIMARY KEY AUTOINCREMENT, facture_id INTEGER, numero INTEGER,
            type_ligne TEXT DEFAULT 'Pièce', designation TEXT DEFAULT '',
            quantite REAL DEFAULT 1, prix_unitaire REAL DEFAULT 0, total REAL DEFAULT 0)""")
        c.execute("""CREATE TABLE IF NOT EXISTS historique_prix (
            id INTEGER PRIMARY KEY AUTOINCREMENT, marque TEXT DEFAULT '',
            modele TEXT DEFAULT '', designation TEXT DEFAULT '',
            prix REAL DEFAULT 0, date_prix TEXT DEFAULT '')""")
        c.execute("CREATE TABLE IF NOT EXISTS parametres (cle TEXT PRIMARY KEY, valeur TEXT)")
        # Archives documentaires : extraction conservée séparément, sans injection automatique
        # dans les fiches clients/devis (évite les faux positifs et les doublons).
        c.execute("""CREATE TABLE IF NOT EXISTS documents_importes (
            id INTEGER PRIMARY KEY AUTOINCREMENT, nom_fichier TEXT NOT NULL,
            chemin_source TEXT DEFAULT '', type_document TEXT DEFAULT '',
            empreinte_sha256 TEXT NOT NULL UNIQUE, texte_extrait TEXT DEFAULT '',
            date_import TEXT DEFAULT '', nb_caracteres INTEGER DEFAULT 0,
            statut TEXT DEFAULT 'À vérifier')""")
        c.execute("CREATE INDEX IF NOT EXISTS i_documents_nom ON documents_importes(nom_fichier)")

        # Migrations : ajoutent les nouveautés sans toucher à vos anciennes données
        _ajouter_colonnes(c, "clients", [("email", "TEXT DEFAULT ''")])
        _ajouter_colonnes(c, "devis", [("version", "INTEGER DEFAULT 1"), ("tva_taux", "REAL DEFAULT 0")])
        _ajouter_colonnes(c, "factures", [("tva_taux", "REAL DEFAULT 0"), ("paye", "INTEGER DEFAULT 0")])

        # Comptabilité (v3) : dates en ISO (AAAA-MM-JJ) pour trier et filtrer correctement
        c.execute("""CREATE TABLE IF NOT EXISTS paiements (
            id INTEGER PRIMARY KEY AUTOINCREMENT, facture_id INTEGER, date_iso TEXT,
            montant REAL DEFAULT 0, mode TEXT DEFAULT 'Espèces', annule INTEGER DEFAULT 0)""")
        _ajouter_colonnes(c, "paiements", [("reference", "TEXT DEFAULT ''")])
        c.execute("""CREATE TABLE IF NOT EXISTS ecritures (
            id INTEGER PRIMARY KEY AUTOINCREMENT, date_iso TEXT, sens TEXT,
            categorie TEXT DEFAULT '', libelle TEXT DEFAULT '', tiers TEXT DEFAULT '',
            montant REAL DEFAULT 0, mode TEXT DEFAULT 'Espèces', piece TEXT DEFAULT '',
            annulee INTEGER DEFAULT 0, cree_le TEXT DEFAULT '')""")
        c.execute("""CREATE TABLE IF NOT EXISTS inventaire (
            annee INTEGER, cle TEXT, valeur REAL DEFAULT 0, PRIMARY KEY (annee, cle))""")
        # Factures déjà marquées payées (v2) : on crée le paiement correspondant, une seule fois
        for f in c.execute("SELECT id, total, date_facture FROM factures WHERE COALESCE(paye,0)=1 "
                           "AND id NOT IN (SELECT facture_id FROM paiements)").fetchall():
            c.execute("INSERT INTO paiements (facture_id, date_iso, montant, mode) VALUES (?,?,?,?)",
                      (f["id"], iso_depuis_fr(f["date_facture"]), f["total"], "Espèces"))

        for idx in (
            "CREATE INDEX IF NOT EXISTS i_devis_immat ON devis(immatriculation)",
            "CREATE INDEX IF NOT EXISTS i_devis_client ON devis(client)",
            "CREATE INDEX IF NOT EXISTS i_ld_devis ON lignes_devis(devis_id)",
            "CREATE INDEX IF NOT EXISTS i_lf_fact ON lignes_facture(facture_id)",
            "CREATE INDEX IF NOT EXISTS i_veh_immat ON vehicules(immatriculation)",
            "CREATE INDEX IF NOT EXISTS i_hp_des ON historique_prix(designation)",
            "CREATE INDEX IF NOT EXISTS i_pai_fact ON paiements(facture_id)",
            "CREATE INDEX IF NOT EXISTS i_pai_date ON paiements(date_iso)",
            "CREATE INDEX IF NOT EXISTS i_ecr_date ON ecritures(date_iso)",
            # V13 : jointures / sous-requêtes de la recherche et du tableau de bord
            "CREATE INDEX IF NOT EXISTS i_veh_client ON vehicules(client_id)",
            "CREATE INDEX IF NOT EXISTS i_fact_immat ON factures(immatriculation)",
            "CREATE INDEX IF NOT EXISTS i_fact_client ON factures(client)",
            "CREATE INDEX IF NOT EXISTS i_pai_cov ON paiements(facture_id, annule, montant)",
            "CREATE INDEX IF NOT EXISTS i_hp_des_nc ON historique_prix(designation COLLATE NOCASE)",
        ):
            c.execute(idx)
        try:  # interdit deux factures pour un même devis
            c.execute("CREATE UNIQUE INDEX IF NOT EXISTS ux_fact_devis ON factures(devis_id)")
        except sqlite3.IntegrityError:
            pass  # anciens doublons déjà présents : on ne bloque pas le démarrage
        c.execute(f"PRAGMA user_version = {SCHEMA_VERSION}")


# ---- Paramètres (garage, TVA, e-mail) -----------------------------------

DEFAUTS = {
    "garage_nom": "CliniqueAutoMada - Entreprise Individuelle",
    "garage_adresse": "Itaosy Ambanilalana 102 Antananarivo",
    "garage_nif": "Numéro NIF: 4011891188 – RCS: 108011015111",
    "garage_contact": "Tél: 0346680206 / 0330339135 | Email: Steeph.szon@gmail.com",
    "tva_taux": "0",
    "smtp_hote": "smtp.gmail.com",
    "smtp_port": "465",
    "smtp_user": "",
    "smtp_mdp": "",
    "auto_envoi": "Non",
    "email_comptable": "",
    # IA optionnelle (nécessite Internet + une clé API Anthropic). "Non" = 100 % hors ligne.
    "ia_active": "Non", "ia_historique": "Non", "ia_cle": "", "ia_modele": "claude-haiku-5-5",
    # Règles fiscales (modifiables si la loi de finances change)
    "is_taux": "5", "is_reduction": "2", "is_plancher": "3", "is_minimum": "0",
}
_CACHE = None


def param(cle):
    global _CACHE
    if _CACHE is None:
        with db() as c:
            _CACHE = {r["cle"]: r["valeur"] for r in c.execute("SELECT cle, valeur FROM parametres")}
    return _CACHE.get(cle, DEFAUTS.get(cle, ""))


def set_param(cle, valeur):
    param(cle)  # force le chargement du cache
    with db() as c:
        c.execute("INSERT OR REPLACE INTO parametres (cle, valeur) VALUES (?, ?)", (cle, valeur))
    _CACHE[cle] = valeur


# ============================================================
# OUTILS
# ============================================================

def _normaliser_calcul(s):
    t = unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode().lower()
    return " ".join(t.split())  # espaces multiples ou en bout de saisie ignorés


_normaliser_cache = functools.lru_cache(maxsize=32768)(_normaliser_calcul)
_RE_NON_ALNUM = re.compile(r"[^a-z0-9]")


@functools.lru_cache(maxsize=32768)
def _compacter_cache(n):
    return _RE_NON_ALNUM.sub("", n)


def normaliser(t):
    """'Tsiférana' -> 'tsiferana' (recherche insensible aux accents et à la casse).
    Appelée des milliers de fois par les requêtes SQL : résultats mis en cache
    (sauf textes très longs, pour ne pas saturer la mémoire)."""
    s = t if isinstance(t, str) else str(t or "")
    return _normaliser_cache(s) if len(s) <= 300 else _normaliser_calcul(s)


def compacter(t):
    """'1921 TBH' / '1921-tbh' -> '1921tbh'."""
    n = normaliser(t)
    return _compacter_cache(n) if len(n) <= 300 else _RE_NON_ALNUM.sub("", n)


def prix_nombre(texte):
    """Convertit les nombres français sans confondre séparateurs de milliers et décimales.

    Les montants suspects restent inchangés en base : cette fonction ne corrige pas leur échelle.
    """
    try:
        if texte is None or isinstance(texte, bool):
            return 0.0
        if isinstance(texte, (int, float)):
            return float(texte)
        val = str(texte).strip().replace("\u00a0", " ").replace("\u202f", " ")
        val = re.sub(r"(?i)\b(ar|ariary|mga)\b", "", val)
        val = re.sub(r"[^0-9, .+\-]", "", val).strip().replace(" ", "")
        if not val or val in ("+", "-"):
            return 0.0
        # Plusieurs séparateurs identiques : groupement de milliers (1.234.567 / 1,234,567).
        if val.count(",") > 1 and "." not in val:
            val = val.replace(",", "")
        elif val.count(".") > 1 and "," not in val:
            val = val.replace(".", "")
        elif "," in val and "." in val:
            # Le dernier séparateur n'est décimal que si 1 ou 2 chiffres le suivent.
            dernier_virgule, dernier_point = val.rfind(","), val.rfind(".")
            sep = "," if dernier_virgule > dernier_point else "."
            pos = val.rfind(sep)
            suffixe = val[pos+1:]
            if len(suffixe) in (1, 2):
                autre = "." if sep == "," else ","
                val = val.replace(autre, "").replace(sep, ".")
            else:
                val = val.replace(",", "").replace(".", "")
        elif "," in val or "." in val:
            sep = "," if "," in val else "."
            morceaux = val.split(sep)
            if len(morceaux) == 2:
                suffixe = morceaux[1]
                if len(suffixe) in (1, 2):
                    val = morceaux[0] + "." + suffixe
                elif len(suffixe) == 3 and morceaux[0].lstrip("+-").isdigit():
                    val = morceaux[0] + suffixe
                else:
                    val = "".join(morceaux)
            else:
                val = "".join(morceaux)
        return float(val) if val not in ("", "+", "-", ".") else 0.0
    except (TypeError, ValueError, OverflowError):
        return 0.0


def email_valide(adresse):
    """Validation simple d'une adresse e-mail avant de l'enregistrer ou de l'envoyer."""
    adresse = str(adresse or "").strip()
    return not adresse or bool(re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", adresse))


def prix_affiche(nombre):
    try:
        return "{:,.0f} Ar".format(float(nombre)).replace(",", " ")
    except Exception:
        return "0 Ar"


def nombre_txt(x):
    try:
        x = float(x)
        return str(int(x)) if x == int(x) else str(x)
    except Exception:
        return "0"


def nom_fichier_sur(texte):
    return re.sub(r"[^A-Za-z0-9_-]", "", str(texte)) or "SANS"


def iso_depuis_fr(texte, strict=False):
    """'05/10/2026' -> '2026-10-05'. En mode strict, une date invalide lève une erreur."""
    try:
        return datetime.strptime(str(texte).strip(), "%d/%m/%Y").strftime("%Y-%m-%d")
    except ValueError:
        if strict:
            raise ValueError("Date invalide : saisissez JJ/MM/AAAA (ex: 05/10/2026).")
        return datetime.now().strftime("%Y-%m-%d")


def fr_depuis_iso(iso):
    try:
        return datetime.strptime(str(iso), "%Y-%m-%d").strftime("%d/%m/%Y")
    except ValueError:
        return str(iso)


def numero_doc(prefixe, doc_id, date_txt=""):
    annee = str(date_txt)[-4:] if len(str(date_txt)) >= 4 else str(datetime.now().year)
    return f"{prefixe}-{annee}-{int(doc_id):04d}"


def totaux(lignes, taux=0.0):
    pieces = sum(l["total"] for l in lignes if l.get("type") != "M.O.")
    mo = sum(l["total"] for l in lignes if l.get("type") == "M.O.")
    ht = pieces + mo
    tva = ht * taux / 100.0
    return {"pieces": pieces, "mo": mo, "ht": ht, "tva": tva, "ttc": round(ht + tva)}


def numero_whatsapp(tel):
    """0346680206 / 034 66 802 06 / +261 34 66 802 06 -> 261346680206"""
    n = "".join(ch for ch in str(tel) if ch.isdigit())
    if n.startswith("00"):
        n = n[2:]
    if n.startswith("261"):
        return n
    if n.startswith("0"):
        n = n[1:]
    return "261" + n if n else ""


def ouvrir_whatsapp(telephone, message):
    n = numero_whatsapp(telephone)
    msg = urllib.parse.quote(str(message))
    url_web = f"https://wa.me/{n}?text={msg}" if n else f"https://wa.me/?text={msg}"
    # Sur Windows, tenter d'abord l'application WhatsApp Desktop si son protocole est installé.
    if platform == "win":
        try:
            os.startfile(f"whatsapp://send?phone={n}&text={msg}")  # noqa: Windows
            return
        except Exception:
            pass
    webbrowser.open(url_web)


def partager_pdf_whatsapp(telephone, message, chemin, titre="Document"):
    """Flux commun de partage WhatsApp pour tous les documents PDF.

    Android transmet le vrai fichier à la feuille de partage. Windows ouvre WhatsApp
    avec le texte préparé et ouvre le PDF; l'ajout du fichier dans le chat reste manuel,
    car wa.me/whatsapp:// n'acceptent pas de chemin de fichier local en pièce jointe.
    La confirmation empêche d'ouvrir le partage par erreur; l'utilisateur garde la
    maîtrise de l'envoi final dans WhatsApp.
    """
    if not chemin or not os.path.isfile(chemin):
        afficher_popup("PDF indisponible", "Le PDF n'existe pas ou n'a pas pu être créé.")
        return

    contenu = BoxLayout(orientation="vertical", spacing=dp(12), padding=dp(14))
    if platform == "android":
        explication = "Le PDF sera transmis au menu de partage. Choisissez WhatsApp, vérifiez le destinataire puis appuyez sur Envoyer."
    else:
        explication = ("WhatsApp va s'ouvrir avec le message préparé et le PDF sera ouvert. "
                       "Pour joindre le fichier, cliquez sur le trombone (+), choisissez Document, "
                       "puis sélectionnez ce PDF. Vérifiez le destinataire avant d'envoyer.")
    contenu.add_widget(Label(text=f"Partager {titre} par WhatsApp ?\n\n{explication}",
                             halign="left", valign="middle", text_size=(dp(430), None)))
    actions = BoxLayout(orientation="horizontal", spacing=dp(10), size_hint_y=None, height=dp(46))
    popup = Popup(title="Confirmation WhatsApp", content=contenu, size_hint=(0.88, None), height=dp(245), auto_dismiss=False)
    btn_annuler = Button(text="Annuler", size_hint_x=0.5)
    btn_continuer = Button(text="Continuer", size_hint_x=0.5)
    actions.add_widget(btn_annuler)
    actions.add_widget(btn_continuer)
    contenu.add_widget(actions)

    def annuler(*_):
        popup.dismiss()

    def continuer(*_):
        popup.dismiss()
        try:
            if platform == "android":
                from androidstorage4kivy import ShareSheet
                ShareSheet().share_file(chemin)
            else:
                ouvrir_whatsapp(telephone, message)
                try:
                    os.startfile(os.path.normpath(chemin))  # noqa: Windows
                except Exception:
                    webbrowser.open("file://" + os.path.abspath(chemin).replace("\\", "/"))
                Clock.schedule_once(lambda dt: afficher_popup(
                    "Dernière étape WhatsApp",
                    "Le message est préparé. Dans WhatsApp, joignez le PDF avec le trombone (+) / Document, "
                    "puis vérifiez le destinataire et appuyez sur Envoyer. L'application ne peut pas joindre "
                    "fiablement un fichier local toute seule via un lien WhatsApp."), 0.4)
        except Exception as e:
            afficher_popup("Partage impossible", str(e))

    btn_annuler.bind(on_release=annuler)
    btn_continuer.bind(on_release=continuer)
    popup.open()


def ouvrir_ou_partager(chemin):
    """Android : feuille de partage (WhatsApp, Gmail, Drive...). Windows : ouvre le PDF."""
    try:
        if platform == "android":
            from androidstorage4kivy import ShareSheet
            ShareSheet().share_file(chemin)
        elif platform == "win":
            os.startfile(chemin)  # noqa
        else:
            webbrowser.open("file://" + chemin)
    except Exception as e:
        afficher_popup("Ouverture impossible", str(e))


def securise(fn):
    """Affiche l'erreur dans un popup au lieu de faire planter l'application."""
    @functools.wraps(fn)
    def wrapper(*a, **k):
        try:
            return fn(*a, **k)
        except Exception as e:
            afficher_popup("Erreur", str(e))
    return wrapper


# ============================================================
# WIDGETS DE BASE
# ============================================================

def bouton(texte, couleur=BLEU, hauteur=48):
    return Button(text=str(texte), font_size=sp(14), bold=True, size_hint_y=None,
                  height=dp(hauteur), background_normal="", background_color=couleur)


def titre(texte):
    return Label(text=str(texte), font_size=sp(21), bold=True, color=BLEU_FONCE,
                 size_hint_y=None, height=dp(45))


def etiquette(texte, taille=12, couleur=GRIS_TEXTE, gras=False, hauteur=20):
    lbl = Label(text=str(texte), font_size=sp(taille), color=couleur, bold=gras,
                halign="left", valign="middle", shorten=True, shorten_from="right",
                size_hint_y=None, height=dp(hauteur))
    lbl.bind(size=lambda i, s: setattr(i, "text_size", s))
    return lbl


def bouton_retour(ecran):
    b = bouton("RETOUR", BLEU_FONCE, 45)
    b.bind(on_release=lambda x: setattr(ecran.manager, "current", "accueil"))
    return b


def afficher_popup(titre_txt, message_txt):
    lbl = Label(text=str(message_txt), font_size=sp(13), halign="center", valign="middle")
    lbl.bind(size=lambda i, s: setattr(i, "text_size", (s[0] - dp(10), None)))
    pop = Popup(title=str(titre_txt), content=lbl, size_hint=(0.88, 0.4))
    pop.open()
    return pop


def popup_actions(titre_txt, message, actions):
    """actions = [(texte, couleur, fonction_ou_None), ...]"""
    box = BoxLayout(orientation="vertical", spacing=dp(8), padding=dp(8))
    lbl = Label(text=str(message), font_size=sp(13), halign="center", valign="middle")
    lbl.bind(size=lambda i, s: setattr(i, "text_size", (s[0] - dp(10), None)))
    box.add_widget(lbl)
    pop = Popup(title=str(titre_txt), content=box, size_hint=(0.9, 0.6))
    for texte, couleur, fn in actions:
        b = bouton(texte, couleur, 42)

        def cliquer(x, f=fn):
            pop.dismiss()
            if f:
                f()
        b.bind(on_release=cliquer)
        box.add_widget(b)
    pop.open()
    return pop


def carte(titre_txt, sous_txt, actions):
    # Les paiements sont séparés des petites actions pour rester visibles sur écran étroit.
    action_avance = next((a for a in actions if ("avance" in str(a[0]).lower() or "paiement" in str(a[0]).lower())), None)
    autres_actions = [a for a in actions if a is not action_avance]
    hauteur = 174 if action_avance else 112
    box = BoxLayout(orientation="vertical", size_hint_y=None, height=dp(hauteur),
                    padding=dp(7), spacing=dp(4))
    box.add_widget(etiquette(titre_txt, 13, BLEU_FONCE, True, 24))
    box.add_widget(etiquette(sous_txt, 11, GRIS_TEXTE, False, 24))
    rangee = BoxLayout(spacing=dp(4), size_hint_y=None, height=dp(38))
    for texte, couleur, fn in autres_actions:
        b = bouton(texte, couleur, 38)
        b.font_size = sp(10)
        b.bind(on_release=fn)
        rangee.add_widget(b)
    box.add_widget(rangee)
    if action_avance:
        _texte, _couleur, fn = action_avance
        b = bouton("AJOUTER UNE AVANCE / UN PAIEMENT", VERT, 48)
        b.font_size = sp(13)
        b.bold = True
        b.bind(on_release=fn)
        box.add_widget(b)
    return box


class TexteDefilant(ScrollView):
    """Texte long qui défile correctement (le Label seul dans un ScrollView ne défile pas)."""

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.lbl = Label(color=BLEU_FONCE, font_size=sp(17), halign="left", valign="top",
                         size_hint_y=None)
        self.lbl.bind(width=lambda i, w: setattr(i, "text_size", (w, None)),
                      texture_size=lambda i, ts: setattr(i, "height", ts[1]))
        self.add_widget(self.lbl)

    def set(self, texte):
        self.lbl.text = texte


# ============================================================
# COUCHE MÉTIER (sans interface)
# ============================================================

def charger_document(type_doc, doc_id):
    if type_doc == "Devis":
        tab, lig, fk, col_date = "devis", "lignes_devis", "devis_id", "date_devis"
    else:
        tab, lig, fk, col_date = "factures", "lignes_facture", "facture_id", "date_facture"
    with db() as c:
        h = c.execute(f"SELECT * FROM {tab} WHERE id=?", (doc_id,)).fetchone()
        if not h:
            raise ValueError(f"{type_doc} introuvable.")
        ls = c.execute(f"SELECT * FROM {lig} WHERE {fk}=? ORDER BY numero", (doc_id,)).fetchall()
        doc = dict(h)
        if type_doc == "Devis":
            doc["km"] = h["kilometrage"]
        else:
            r = c.execute("SELECT kilometrage FROM devis WHERE id=?", (h["devis_id"],)).fetchone()
            doc["km"] = r["kilometrage"] if r else ""
        cl = c.execute("SELECT telephone, email FROM clients WHERE norm(nom)=norm(?) LIMIT 1",
                       (h["client"],)).fetchone()
        v = c.execute("SELECT moteur, vin FROM vehicules WHERE compact(immatriculation)=compact(?) "
                      "ORDER BY id DESC LIMIT 1", (h["immatriculation"],)).fetchone()
    doc["tel"] = cl["telephone"] if cl else ""
    doc["email"] = (cl["email"] if cl else "") or ""
    doc["moteur"] = v["moteur"] if v else ""
    doc["vin"] = (v["vin"] if v else "") or ""
    doc["date"] = h[col_date]
    doc["version"] = int(doc.get("version") or 1)
    doc["tva_taux"] = float(doc.get("tva_taux") or 0)
    doc["lignes"] = [{"type": l["type_ligne"], "designation": l["designation"],
                      "quantite": l["quantite"], "prix": l["prix_unitaire"],
                      "total": l["total"]} for l in ls]
    return doc


def dernier_prix(designation, vehicule=""):
    """Dernier prix utilisé pour cette désignation (priorité au même véhicule)."""
    with db() as c:
        r = c.execute("SELECT prix FROM historique_prix WHERE designation=? COLLATE NOCASE "
                      "ORDER BY (marque=? COLLATE NOCASE) DESC, id DESC LIMIT 1",
                      (designation, vehicule)).fetchone()
    return r["prix"] if r else 0



# ---- OFFLINE_BEGIN
DERNIERES_NOTES = []

_MOTS_VIDES = {"de", "du", "des", "la", "le", "les", "l", "d", "a", "au", "aux", "un", "une",
               "pour", "et", "en", "sur", "avec", "the"}
_SYNONYMES = {"av": "avant", "ar": "arriere", "arr": "arriere", "clim": "habitacle",
              "pollen": "habitacle", "cabine": "habitacle", "gasoil": "carburant",
              "gazoil": "carburant", "diesel": "carburant", "essence": "carburant"}
_GR_FILTRE = {"huile", "air", "habitacle", "carburant"}
_GR_POSITION = {"avant", "arriere"}
_AVEC_POSITION = {"plaquette", "disque", "amortisseur", "tambour", "machoire"}
_DEBUTS_PHRASE = {"elle", "il", "ils", "elles", "veut", "veux", "voudrait", "svp", "devis",
                  "pour", "client", "cliente", "mme", "mr", "madame", "monsieur", "vehicule",
                  "voiture", "merci", "bonjour", "je", "on", "faire", "fais", "fait"}
_RE_MO = re.compile(r"^(?:vidange|remplacement|changement|pose|depose|montage|demontage|purge|"
                    r"nettoyage|controle|diagnostic|reglage|reparation|revision|geometrie|"
                    r"equilibrage|parallelisme|decalaminage|main d)")
_RE_DIESEL = re.compile(r"\b(diesel|gasoil|gazoil|dci|hdi|tdi|cdi|crdi|k9k|d4cb|d4bh|d4ea)\b")


_RE_VISCOSITE = re.compile(r"\d+w?")


@functools.lru_cache(maxsize=16384)
def _mots_cle_cache(n):
    res = set()
    for w in re.findall(r"[a-z0-9]+", n):
        if w in _MOTS_VIDES or _RE_VISCOSITE.fullmatch(w):
            continue
        w = _SYNONYMES.get(w, w)
        if len(w) > 3 and w.endswith("s"):
            w = w[:-1]
        res.add(w)
    return frozenset(res)


def _mots_cle(texte):
    """Mots significatifs d'une désignation (sans accents, au singulier, sans viscosité).
    Retourne un frozenset mis en cache."""
    n = normaliser(texte)
    return _mots_cle_cache(n) if len(n) <= 300 else _mots_cle_cache.__wrapped__(n)


def _compatibles(R, C):
    """Interdit les confusions classiques : filtre à huile / à air, avant / arrière."""
    if "filtre" in R or "filtre" in C:
        a, b = R & _GR_FILTRE, C & _GR_FILTRE
        if "filtre" in R and not a:
            return False            # « filtre » seul : trop ambigu pour proposer un prix
        if a and b and a != b:
            return False
    a, b = R & _GR_POSITION, C & _GR_POSITION
    if a and b and a != b:
        return False
    if (R & _AVEC_POSITION) and not a and b:
        return False                # « plaquettes » sans position vs historique « avant »
    return True


def _extraire_km(texte):
    t = normaliser(texte)
    m = (re.search(r"km\s*[:=]?\s*(\d[\d .]{2,9}\d)", t)
         or re.search(r"(\d[\d .]{2,9}\d)\s*km", t))
    if not m:
        return 0
    n = int(re.sub(r"\D", "", m.group(1)) or 0)
    return n if 0 < n < 2000000 else 0


def _forfait_revision(complete, km, diesel):
    P, MO = "Pièce", "M.O."
    note_dist = ("Kilométrage élevé : remplacement recommandé, à vérifier avec le carnet"
                 if km >= 100000 else "À vérifier avec le carnet d'entretien")
    L = [(P, "Huile moteur 5W-40", 5.0, ""), (P, "Filtre à huile", 1.0, ""),
         (P, "Filtre à air", 1.0, "")]
    if not complete:
        return L + [(MO, "Vidange moteur", 1.0, "")]
    L.append((P, "Filtre habitacle", 1.0, ""))
    L.append((P, "Filtre à gasoil", 1.0, "") if diesel else (P, "Bougies d'allumage", 4.0, ""))
    dist = (km == 0 or km >= 100000)
    if dist:
        L.append((P, "Kit distribution + pompe à eau", 1.0, note_dist))
    L += [(P, "Courroie d'accessoires", 1.0, ""), (P, "Liquide de refroidissement", 1.0, ""),
          (P, "Liquide de frein", 1.0, ""), (P, "Plaquettes de frein avant", 1.0, "À confirmer après inspection"),
          (MO, "Vidange moteur", 1.0, "")]
    if dist:
        L.append((MO, "Remplacement kit distribution et pompe à eau", 1.0, ""))
    L.append((MO, "Remplacement courroie d'accessoires" if diesel
              else "Remplacement bougies et courroie d'accessoires", 1.0, ""))
    L += [(MO, "Purge du circuit de refroidissement", 1.0, ""),
          (MO, "Remplacement liquide de frein et purge", 1.0, ""),
          (MO, "Remplacement plaquettes avant, contrôle freins arrière", 1.0, "")]
    if not diesel:
        L.append((MO, "Nettoyage du corps de papillon", 1.0, ""))
    L.append((MO, "Contrôle général (suspension, direction, pneus, éclairage, fuites)", 1.0, ""))
    return L


_LEXIQUE = [  # (motif sur texte normalisé, type, désignation, quantité)
    (r"kit distribution|courroie (?:de )?distribution|\bdistribution\b", "Pièce", "Kit distribution", 1.0),
    (r"pompe a eau", "Pièce", "Pompe à eau", 1.0),
    (r"courroie (?:d )?accessoires?", "Pièce", "Courroie d'accessoires", 1.0),
    (r"huile (?:de )?moteur|huile 5w|huile 10w|huile 15w", "Pièce", "Huile moteur 5W-40", 5.0),
    (r"filtre (?:a )?huile", "Pièce", "Filtre à huile", 1.0),
    (r"filtre (?:a )?air", "Pièce", "Filtre à air", 1.0),
    (r"filtre (?:d )?(?:habitacle|cabine|pollen|clim\w*)", "Pièce", "Filtre habitacle", 1.0),
    (r"filtre (?:a )?(?:carburant|gasoil|gazoil|essence)", "Pièce", "Filtre à carburant", 1.0),
    (r"bougies?", "Pièce", "Bougies d'allumage", 4.0),
    (r"plaquettes?(?: de frein)?(?: (avant|arriere))?", "Pièce", "Plaquettes de frein", 1.0),
    (r"disques?(?: de frein)?(?: (avant|arriere))?", "Pièce", "Disques de frein", 2.0),
    (r"liquide (?:de )?frein", "Pièce", "Liquide de frein", 1.0),
    (r"liquide (?:de )?refroidissement|antigel", "Pièce", "Liquide de refroidissement", 1.0),
    (r"amortisseurs?(?: (avant|arriere))?", "Pièce", "Amortisseurs", 2.0),
    (r"batterie", "Pièce", "Batterie", 1.0),
    (r"embrayage", "Pièce", "Kit embrayage", 1.0),
    (r"vidange", "M.O.", "Vidange moteur", 1.0),
]


def _lexique(n):
    """Éléments connus repérés dans une phrase libre (texte déjà normalisé)."""
    trouves = []
    for motif, typ, des, q in _LEXIQUE:
        m = re.search(motif, n)
        if m:
            if m.lastindex and m.group(m.lastindex):
                des += " " + m.group(m.lastindex)
            trouves.append((typ, des, q))
    return trouves


def suggerer_lignes_devis_hors_ligne(texte, vehicule="", km="", moteur=""):
    """Prépare des lignes de devis à partir d'un texte, sans écrire dans la base.

    Comprend : une ligne par élément, « 2 x filtre », « 4 bougies », la numérotation,
    les virgules, les forfaits (« révision totale / simple ») et les phrases libres.
    Les prix viennent uniquement de l'historique, jamais inventés."""
    del DERNIERES_NOTES[:]
    texte = str(texte or "")
    if not texte.strip():
        return []
    km_v = int(prix_nombre(km) or 0) or _extraire_km(texte)
    diesel = bool(_RE_DIESEL.search(normaliser(f"{texte} {moteur} {vehicule}")))

    demandes, vus = [], set()

    def ajouter(typ, des, q, note=""):
        cle = (typ, normaliser(des))
        if des and cle not in vus:
            vus.add(cle)
            demandes.append({"type": typ, "designation": des, "quantite": q, "prix": 0.0,
                             "source_prix": "À confirmer", "note": note})

    for bloc in re.split(r"\n+|;|,(?!\d)", texte):
        bloc = bloc.strip(" \t-•*·")
        bloc = re.sub(r"^\(?\d{1,2}\s*[.)]\s+", "", bloc)       # numérotation « 1. »
        if not bloc:
            continue
        quantite = 1.0
        m = re.match(r"^\s*(\d+(?:[.,]\d+)?)\s*(?:x|×)\s*(.+)$", bloc, re.I) \
            or re.match(r"^\s*(\d{1,2})\s+(?![x×]\b)([^\W\d].*)$", bloc, re.I)
        if m:
            quantite = prix_nombre(m.group(1)) or 1.0
            bloc = m.group(2).strip()
        est_mo = bool(re.match(r"^(?:m\.?o\.?|main\s*d.?oeuvre)\b", bloc, re.I))
        n = normaliser(bloc)

        if not est_mo:  # forfaits
            if re.search(r"petite revision|revision simple|revision legere|entretien courant", n):
                for t, d, q, no in _forfait_revision(False, km_v, diesel):
                    ajouter(t, d, q, no)
                continue
            if re.search(r"\brevision\b|grand entretien|full service", n):
                for t, d, q, no in _forfait_revision(True, km_v, diesel):
                    ajouter(t, d, q, no)
                continue

        mots = n.split()
        phrase = len(mots) > 6 or (mots and mots[0] in _DEBUTS_PHRASE)
        if phrase and not est_mo:
            for t, d, q in _lexique(n):
                ajouter(t, d, quantite if (len(_lexique(n)) == 1 and quantite != 1.0) else q)
            continue

        designation = re.sub(r"^(?:m\.?o\.?\s*[:=-]?\s*|main\s*d.?oeuvre\s*[:=-]?\s*)",
                             "", bloc, flags=re.I).strip()
        ajouter("M.O." if (est_mo or _RE_MO.match(normaliser(designation))) else "Pièce",
                designation, quantite)

    if not demandes:
        DERNIERES_NOTES.append("Aucune pièce ni prestation reconnue dans ce texte.")
    return appliquer_prix_historique(demandes, vehicule)


def appliquer_prix_historique(demandes, vehicule=""):
    """Associe à chaque ligne le prix déjà utilisé dans l'historique (jamais inventé).

    Utilisé par l'assistant hors ligne ET par l'IA. Un contrôle empêche les confusions
    (filtre à huile / filtre à air, avant / arrière)."""
    if not demandes:
        return []
    candidats = _candidats_prix()
    marque_cible = normaliser(vehicule)
    for demande in demandes:
        corr = _correspondances(demande["designation"], candidats, marque_cible)
        if corr:
            meilleur = max(corr, key=lambda x: x["score"])["cand"]   # à égalité : le plus récent
            demande["prix"] = meilleur["prix"]
            demande["source_prix"] = "Historique : " + meilleur["designation"]
        else:
            demande["source_prix"] = "Aucun prix fiable : saisir le P.U."
    return demandes
# ---- OFFLINE_END


# ---- ASSISTANT_V96_BEGIN
# ============================================================
# V9.6 : fiches client/véhicule, contrôle du devis, questions sur l'historique
# (tout ce bloc fonctionne hors ligne ; l'IA n'est qu'une aide en plus)
# ============================================================

# ---- A. Fiches client / véhicule : remplissage automatique ----------------

_RE_TITRE = re.compile(r"^(?:mme|mlle|mr|m|madame|monsieur|mademoiselle|dr|docteur)\b\.?\s*")


def _nom_sans_titre(nom):
    return _RE_TITRE.sub("", normaliser(nom)).strip()


def _fiches_du_client(c, cl):
    base = {"client": cl["nom"] or "", "telephone": cl["telephone"] or "", "email": cl["email"] or ""}
    vs = c.execute("SELECT * FROM vehicules WHERE client_id=? ORDER BY id DESC", (cl["id"],)).fetchall()
    if not vs:
        return [dict(base)]
    res = []
    for v in vs:
        f = dict(base)
        f.update(marque=v["marque"] or "", immat=v["immatriculation"] or "",
                 moteur=v["moteur"] or "", vin=v["vin"] or "", km=str(v["kilometrage"] or ""))
        res.append(f)
    return res


def _fiche_par_immat(c, cible):
    v = c.execute("SELECT * FROM vehicules WHERE compact(immatriculation)=? ORDER BY id DESC LIMIT 1",
                  (cible,)).fetchone()
    if not v:
        return None
    cl = c.execute("SELECT * FROM clients WHERE id=?", (v["client_id"],)).fetchone()
    if cl:
        for f in _fiches_du_client(c, cl):
            if compacter(f.get("immat", "")) == cible:
                return f
    return {"client": "", "telephone": "", "email": "", "marque": v["marque"] or "",
            "immat": v["immatriculation"] or "", "moteur": v["moteur"] or "",
            "vin": v["vin"] or "", "km": str(v["kilometrage"] or "")}


def chercher_fiche(champ, valeur):
    """Cherche une fiche existante selon ce que l'on vient de saisir.

    champ : 'immat', 'client', 'email' ou 'telephone'.
    Retourne {'statut': 'exact' | 'proche' | 'aucun', 'fiches': [...]}.
    'proche' = faute de frappe probable : la fiche trouvée doit être confirmée."""
    valeur = str(valeur or "").strip()
    rien = {"statut": "aucun", "fiches": []}
    if len(valeur) < 3:
        return rien
    with db() as c:
        if champ == "immat":
            cible = compacter(valeur)
            f = _fiche_par_immat(c, cible)
            if f:
                return {"statut": "exact", "fiches": [f]}
            plaques = {compacter(r[0]) for r in c.execute(
                "SELECT immatriculation FROM vehicules UNION SELECT immatriculation FROM devis")
                if r[0] and len(compacter(r[0])) >= 4}
            for p in difflib.get_close_matches(cible, sorted(plaques), n=1, cutoff=0.8):
                if abs(len(p) - len(cible)) <= 1:
                    f = _fiche_par_immat(c, p)
                    if f:
                        return {"statut": "proche", "fiches": [f]}
            return rien

        clients = c.execute("SELECT * FROM clients ORDER BY id DESC").fetchall()
        if champ == "client":
            cible = _nom_sans_titre(valeur)
            if len(cible) < 3:
                return rien
            for cl in clients:
                if _nom_sans_titre(cl["nom"]) == cible:
                    return {"statut": "exact", "fiches": _fiches_du_client(c, cl)}
            meilleur, score = None, 0.0
            for cl in clients:
                n = _nom_sans_titre(cl["nom"])
                sm = difflib.SequenceMatcher(None, cible, n)
                # bornes supérieures bon marché : inutile de calculer ratio() si < 0.8
                if sm.real_quick_ratio() >= 0.8 and sm.quick_ratio() >= 0.8:
                    s = sm.ratio()
                else:
                    s = 0.0
                if any(t.startswith(cible) for t in n.split()) and len(cible) >= 4:
                    s = max(s, 0.85)             # début de nom tapé
                if s > score:
                    meilleur, score = cl, s
            if meilleur is not None and score >= 0.8:
                return {"statut": "proche", "fiches": _fiches_du_client(c, meilleur)}
            return rien
        if champ == "email":
            for cl in clients:
                if (cl["email"] or "").strip().lower() == valeur.lower():
                    return {"statut": "exact", "fiches": _fiches_du_client(c, cl)}
            return rien
        if champ == "telephone":
            cle = re.sub(r"\D", "", valeur)[-9:]
            if len(cle) < 7:
                return rien
            for cl in clients:
                if re.sub(r"\D", "", cl["telephone"] or "")[-9:] == cle:
                    return {"statut": "exact", "fiches": _fiches_du_client(c, cl)}
    return rien


def dernier_km(immat):
    """(kilométrage, date) du dernier devis connu pour cette plaque."""
    with db() as c:
        r = c.execute("SELECT kilometrage, date_devis FROM devis "
                      "WHERE compact(immatriculation)=compact(?) AND COALESCE(kilometrage,'')<>'' "
                      "ORDER BY id DESC LIMIT 1", (immat,)).fetchone()
    return (int(prix_nombre(r["kilometrage"]) or 0), r["date_devis"]) if r else (0, "")


_DOMAINES = {"gmial.com": "gmail.com", "gmai.com": "gmail.com", "gamil.com": "gmail.com",
             "gmail.con": "gmail.com", "gmail.co": "gmail.com", "gmail.cm": "gmail.com",
             "gmaill.com": "gmail.com", "gnail.com": "gmail.com", "gmail.om": "gmail.com",
             "yahooo.fr": "yahoo.fr", "yaho.fr": "yahoo.fr", "yahou.fr": "yahoo.fr",
             "yahoo.con": "yahoo.com", "hotmial.com": "hotmail.com", "hotmal.com": "hotmail.com",
             "hotmail.con": "hotmail.com", "outlok.com": "outlook.com", "outlook.con": "outlook.com"}


def corriger_email(adresse):
    """Propose une correction (faute de domaine, espaces) ou None."""
    brut = str(adresse or "").strip()
    a = brut.lower().replace(" ", "")
    if "@" not in a:
        return None
    local, _, dom = a.rpartition("@")
    if dom in _DOMAINES:
        return f"{local}@{_DOMAINES[dom]}"
    if a != brut.lower() and email_valide(a):
        return a
    return None


# ---- B. Lire un texte libre (client, véhicule, km...) ---------------------

_MARQUES = {
    "duster": "Dacia Duster", "logan": "Dacia Logan", "sandero": "Dacia Sandero",
    "clio": "Renault Clio", "megane": "Renault Mégane", "kangoo": "Renault Kangoo",
    "twingo": "Renault Twingo", "captur": "Renault Captur", "hilux": "Toyota Hilux",
    "corolla": "Toyota Corolla", "yaris": "Toyota Yaris", "rav4": "Toyota RAV4",
    "land cruiser": "Toyota Land Cruiser", "prado": "Toyota Prado", "hiace": "Toyota Hiace",
    "terracan": "Hyundai Terracan", "tucson": "Hyundai Tucson", "santa fe": "Hyundai Santa Fe",
    "i10": "Hyundai i10", "picanto": "Kia Picanto", "sportage": "Kia Sportage",
    "sorento": "Kia Sorento", "l200": "Mitsubishi L200", "pajero": "Mitsubishi Pajero",
    "partner": "Peugeot Partner", "berlingo": "Citroën Berlingo", "golf": "Volkswagen Golf",
    "polo": "Volkswagen Polo", "ranger": "Ford Ranger", "fiesta": "Ford Fiesta",
    "navara": "Nissan Navara", "qashqai": "Nissan Qashqai", "swift": "Suzuki Swift",
    "vitara": "Suzuki Vitara", "jimny": "Suzuki Jimny",
}
_RE_EMAIL = re.compile(r"[\w.+-]+@[\w-]+(?:\.[\w-]+)+")
_RE_TEL = re.compile(r"(?<!\d)(?:\+?261[\s.-]?|0)3\d(?:[\s.-]?\d){7}(?!\d)")
_RE_VIN = re.compile(r"\b[A-HJ-NPR-Z0-9]{17}\b")
_RE_PLAQUE = re.compile(r"(?<![\w])(\d{3,4})\s?-?\s?([A-Za-z]{3})(?![A-Za-z0-9])")
_PAS_PLAQUE = {"les", "des", "une", "est", "pas", "sur", "par", "ces", "ses", "mes", "nos", "vos",
               "mme", "mlle", "bmw", "kia", "kms", "ans", "fois", "non", "oui", "dci", "hdi", "tdi"}


def _trouver_plaque(t):
    for m in _RE_PLAQUE.finditer(t):
        chiffres, lettres = m.group(1), m.group(2)
        if lettres.lower() in _PAS_PLAQUE:
            continue
        if re.fullmatch(r"(?:19|20)\d\d", chiffres) and not lettres.isupper():
            continue                       # « 2011 des » : une année, pas une plaque
        return m
    return None


def extraire_infos_texte(texte):
    """Repère dans une phrase libre le client, le véhicule, le km, le téléphone, etc.
    Retourne seulement ce qui a été trouvé (clés : client, telephone, email, immat, vin,
    marque, moteur, km)."""
    t = str(texte or "")
    n = normaliser(t)
    res = {}
    m = _RE_EMAIL.search(t)
    if m:
        res["email"] = m.group(0).lower()
    m = _RE_TEL.search(t)
    if m:
        res["telephone"] = re.sub(r"[^\d+]", "", m.group(0))
    m = _RE_VIN.search(t.upper())
    if m and re.search(r"[A-Z]", m.group(0)) and re.search(r"\d", m.group(0)):
        res["vin"] = m.group(0)
    m = _trouver_plaque(t)
    if m:
        res["immat"] = (m.group(1) + m.group(2)).upper()
    km = _extraire_km(t)
    if km:
        res["km"] = str(km)

    m = re.search(r"\bmoteur\s+(?:[a-z]+\s+){0,3}?([a-z]*\d[a-z0-9\-]{1,7})\b", n)
    if not m:
        m = re.search(r"\b([kdfjrg]\d[a-z]{1,2}\d{0,2})\b", n)
    if m:
        res["moteur"] = m.group(1).upper()

    annee = re.search(r"\b(19[89]\d|20[0-3]\d)\b", n)
    with db() as c:
        connues = {normaliser(r[0]): r[0] for r in c.execute(
            "SELECT DISTINCT marque FROM vehicules WHERE LENGTH(COALESCE(marque,''))>=4")}
        noms = [r[0] for r in c.execute("SELECT nom FROM clients")]
    marque = None
    for cle in sorted(connues, key=len, reverse=True):
        if re.search(r"\b" + re.escape(cle) + r"\b", n):
            marque = connues[cle]
            break
    if not marque:
        for cle in sorted(_MARQUES, key=len, reverse=True):
            if re.search(r"\b" + re.escape(cle) + r"\b", n):
                marque = _MARQUES[cle]
                break
    if marque:
        res["marque"] = marque + (f" {annee.group(1)}" if annee and annee.group(1) not in marque else "")

    meilleur = None
    for nom in noms:
        cn = _nom_sans_titre(nom)
        toks = [w for w in cn.split() if len(w) >= 3]
        if toks and all(re.search(r"\b" + re.escape(w) + r"\b", n) for w in toks):
            if meilleur is None or len(cn) > len(meilleur[1]):
                meilleur = (nom, cn)
    if meilleur:
        res["client"] = meilleur[0]
    else:
        m = re.search(r"\b(mme|mlle|mr|madame|monsieur|mademoiselle)\.?\s+([a-z'\-]{3,})", n)
        if m:
            titre_ = {"madame": "MME", "monsieur": "MR", "mademoiselle": "MLLE"}.get(m.group(1), m.group(1).upper())
            res["client"] = f"{titre_} {m.group(2).upper()}"
    return res


def anonymiser_texte(texte):
    """Retire du texte tout ce qui identifie le client avant un envoi à l'IA."""
    t = str(texte or "")
    t = _RE_EMAIL.sub(" ", t)
    t = _RE_TEL.sub(" ", t)
    t = _RE_VIN.sub(" ", t)
    m = _trouver_plaque(t)
    if m:
        t = t[:m.start()] + " " + t[m.end():]
    with db() as c:
        noms = [r[0] for r in c.execute("SELECT nom FROM clients")]
    jetons = {w for nom in noms for w in _nom_sans_titre(nom).split() if len(w) >= 3}
    infos = extraire_infos_texte(t)
    if infos.get("client"):
        jetons |= {w for w in _nom_sans_titre(infos["client"]).split() if len(w) >= 3}
    for w in jetons:
        t = re.sub(r"\b" + re.escape(w) + r"\b", " ", t, flags=re.I)
    t = re.sub(r"\b(?:mme|mlle|mr|madame|monsieur|mademoiselle)\b\.?", " ", t, flags=re.I)
    return re.sub(r"[ \t]+", " ", t).strip()


# ---- C. Contrôle du devis : prix, quantités, types, doublons ---------------

_LIQUIDES = {"huile", "liquide", "graisse", "peinture", "antigel", "produit", "nettoyant",
             "carburant", "litre", "vernis", "mastic", "colle", "lubrifiant"}
_MAX_TYPIQUE = {"filtre": 4, "bougie": 8, "plaquette": 4, "disque": 4, "amortisseur": 4, "pneu": 6,
                "batterie": 2, "courroie": 3, "bobine": 4, "injecteur": 6, "rotule": 4,
                "roulement": 4, "joint": 8, "kit": 3}
_MOTS_PIECE = {"filtre", "bougie", "plaquette", "disque", "huile", "courroie", "kit", "amortisseur",
               "batterie", "pneu", "liquide", "joint", "pompe", "rotule", "embrayage", "alternateur",
               "demarreur", "injecteur", "bobine", "roulement", "radiateur", "durite", "capteur", "sonde"}
_RE_VERBE_MO = re.compile(r"^(?:vidange|remplacement|changement|pose|depose|montage|demontage|purge|"
                          r"nettoyage|controle|diagnostic|reglage|reparation|geometrie|equilibrage|"
                          r"parallelisme|decalaminage|main d)")


_CAND_CACHE = {"sig": None, "val": None}


def _candidats_prix():
    """Candidats de prix (historique + devis + factures), reconstruits seulement si les
    données ont changé (signature = nombre de lignes et plus grand id de chaque table)."""
    with db() as c:
        sig = tuple(tuple(c.execute(q).fetchone()) for q in (
            "SELECT COUNT(*), COALESCE(MAX(id),0) FROM historique_prix",
            "SELECT COUNT(*), COALESCE(MAX(id),0) FROM lignes_devis",
            "SELECT COUNT(*), COALESCE(MAX(id),0) FROM lignes_facture",
            "SELECT COUNT(*), COALESCE(MAX(id),0) FROM devis",
            "SELECT COUNT(*), COALESCE(MAX(id),0) FROM factures"))
    if _CAND_CACHE["sig"] == sig and _CAND_CACHE["val"] is not None:
        return _CAND_CACHE["val"]
    val = _construire_candidats_prix()
    _CAND_CACHE["sig"], _CAND_CACHE["val"] = sig, val
    return val


def _construire_candidats_prix():
    with db() as c:
        historiques = c.execute(
            "SELECT designation, prix, marque FROM historique_prix "
            "WHERE COALESCE(prix,0)>0 ORDER BY id DESC LIMIT 2000").fetchall()
        precedents = c.execute(
            "SELECT l.designation, l.prix_unitaire AS prix, d.vehicule AS marque "
            "FROM lignes_devis l JOIN devis d ON d.id=l.devis_id "
            "WHERE COALESCE(l.prix_unitaire,0)>0 ORDER BY l.id DESC LIMIT 2000").fetchall()
        try:
            factures = c.execute(
                "SELECT l.designation, l.prix_unitaire AS prix, f.vehicule AS marque "
                "FROM lignes_facture l JOIN factures f ON f.id=l.facture_id "
                "WHERE COALESCE(l.prix_unitaire,0)>0 ORDER BY l.id DESC LIMIT 2000").fetchall()
        except Exception:
            factures = []
    candidats, vus = [], set()
    for r in list(historiques) + list(precedents) + list(factures):  # du plus récent au plus ancien
        nom = str(r["designation"] or "").strip()
        prix = prix_nombre(r["prix"])
        marque = normaliser(r["marque"] or "")
        cle = (normaliser(nom), prix, marque)
        if nom and prix > 0 and cle not in vus:
            vus.add(cle)
            candidats.append({"designation": nom, "prix": prix, "marque": marque,
                              "norm": normaliser(nom), "mots": _mots_cle(nom)})
    return candidats


def _correspondances(designation, candidats, marque_cible=""):
    """Toutes les entrées d'historique qui correspondent, avec un score."""
    R = _mots_cle(designation)
    cible = normaliser(designation)
    res = []
    for cand in candidats:
        C = cand["mots"]
        if not R or not C or not _compatibles(R, C):
            continue
        inter = len(R & C)
        if inter == 0 and abs(len(cible) - len(cand["norm"])) > 3:
            continue                                   # aucun mot commun : inutile d'aller plus loin
        cont, jac = inter / len(R), inter / len(R | C)
        sm = difflib.SequenceMatcher(None, cible, cand["norm"])
        mots_ok = (cont == 1.0 and jac >= 0.25) or (cont >= 0.75 and len(R) >= 4 and jac >= 0.5)
        if not mots_ok and (sm.real_quick_ratio() < 0.9 or sm.quick_ratio() < 0.9):
            continue
        ratio = sm.ratio()
        if not (mots_ok or ratio >= 0.9):
            continue
        score = 0.6 * cont + 0.3 * jac + 0.1 * ratio
        meme_vehicule = bool(marque_cible and cand["marque"] and (
            marque_cible in cand["marque"] or cand["marque"] in marque_cible))
        if meme_vehicule:
            score += 0.05
        res.append({"score": score, "cand": cand, "meme_vehicule": meme_vehicule})
    return res


def prix_reference(designation, vehicule, candidats):
    """{'n', 'dernier', 'mediane', 'designation'} d'après l'historique, ou None."""
    corr = _correspondances(designation, candidats, normaliser(vehicule))
    if not corr:
        return None
    meilleur = max(corr, key=lambda x: x["score"])   # à égalité : le plus récent
    memes = [x for x in corr if x["meme_vehicule"]] or corr
    prix = [x["cand"]["prix"] for x in memes]
    return {"n": len(prix), "dernier": meilleur["cand"]["prix"],
            "mediane": statistics.median(prix), "designation": meilleur["cand"]["designation"]}


def controler_devis(lignes, vehicule="", km=0):
    """Vérifie les lignes d'un devis : retourne une liste d'anomalies
    {ligne, niveau (erreur|alerte|info), message, action, correction}.
    Rien n'est modifié : l'utilisateur choisit quoi appliquer."""
    issues = []
    cands = _candidats_prix()
    noms = {c["norm"]: c["designation"] for c in cands}

    def add(i, niveau, message, correction=None, action="modifier", refs=0):
        detail = message.split(" : ", 1)[1] if (i is not None and " : " in message) else message
        issues.append({"ligne": i, "niveau": niveau, "message": message, "detail": detail,
                       "action": action, "correction": correction, "references": refs})

    vus = {}
    a_piece = a_mo = False
    for i, l in enumerate(lignes):
        des = str(l.get("designation", "")).strip()
        q = prix_nombre(l.get("quantite", 0))
        p = prix_nombre(l.get("prix", 0))
        typ = l.get("type", "Pièce")
        if not des:
            if q or p:
                add(i, "erreur", f"Ligne {i + 1} : désignation manquante.")
            continue
        n = normaliser(des)
        mots = _mots_cle(des)
        etiquette_l = f"Ligne {i + 1} « {des[:32]} »"
        if typ == "M.O.":
            a_mo = True
        else:
            a_piece = True

        # type pièce / main d'oeuvre
        if typ == "Pièce" and _RE_VERBE_MO.match(n):
            add(i, "alerte", f"{etiquette_l} : ressemble à de la main d'oeuvre, classée « Pièce ».",
                {"type": "M.O."})
        elif typ == "M.O." and n.split() and n.split()[0].rstrip("s") in _MOTS_PIECE \
                and not _RE_VERBE_MO.match(n):
            add(i, "alerte", f"{etiquette_l} : ressemble à une pièce, classée « M.O. ».",
                {"type": "Pièce"})

        # quantité
        if q < 0 or (q == 0 and (p or des)):
            add(i, "erreur", f"{etiquette_l} : quantité {nombre_txt(q)} impossible.", {"quantite": 1})
        else:
            if typ == "Pièce" and q != int(q) and not (mots & _LIQUIDES):
                add(i, "alerte", f"{etiquette_l} : quantité décimale ({nombre_txt(q)}) pour une pièce.",
                    {"quantite": max(1, round(q))})
            mx = next((v for k, v in _MAX_TYPIQUE.items() if k in mots), 12)
            if typ == "Pièce" and q > mx and not (mots & _LIQUIDES - {"liquide"} and q <= 12):
                add(i, "alerte", f"{etiquette_l} : quantité {nombre_txt(q)} inhabituelle "
                                 f"(en général {mx} au plus). Faute de frappe ?")
            elif typ == "M.O." and q > 20:
                add(i, "alerte", f"{etiquette_l} : {nombre_txt(q)} unités de main d'oeuvre, vérifiez.")
            if "huile" in mots and "filtre" not in mots and q > 12:
                add(i, "alerte", f"{etiquette_l} : {nombre_txt(q)} litres d'huile, vérifiez.")

        # prix
        ref = prix_reference(des, vehicule, cands)
        if p < 0:
            add(i, "erreur", f"{etiquette_l} : prix négatif.", {"prix": abs(p)})
        elif p == 0:
            corr = {"prix": ref["dernier"]} if ref else None
            add(i, "alerte", f"{etiquette_l} : prix manquant"
                + (f" ; historique : {prix_affiche(ref['dernier'])}." if ref else "."), corr,
                refs=ref["n"] if ref else 0)
        elif ref:
            base = ref["mediane"] if ref["n"] >= 3 else ref["dernier"]
            r = p / base if base else 1
            hist = f"historique ≈ {prix_affiche(base)}"
            if abs(p * 10 / base - 1) < 0.25:
                add(i, "alerte", f"{etiquette_l} : {prix_affiche(p)} — il manque peut-être un zéro "
                                 f"({hist}).", {"prix": p * 10}, refs=ref["n"])
            elif abs(p / 10 / base - 1) < 0.25:
                add(i, "alerte", f"{etiquette_l} : {prix_affiche(p)} — un zéro en trop peut-être "
                                 f"({hist}).", {"prix": p / 10}, refs=ref["n"])
            elif r > 2.0 or r < 0.5:
                add(i, "alerte", f"{etiquette_l} : {prix_affiche(p)} très différent de l'historique "
                                 f"({prix_affiche(base)}).", {"prix": base}, refs=ref["n"])
            elif r > 1.4 or r < 0.71:
                add(i, "info", f"{etiquette_l} : {prix_affiche(p)}, écart de {round((r - 1) * 100):+d} % "
                               f"avec l'historique ({prix_affiche(base)}).", {"prix": base}, refs=ref["n"])
        elif len(n) >= 5:  # pas de référence : peut-être une faute dans la désignation
            for proche in difflib.get_close_matches(n, list(noms), n=1, cutoff=0.84):
                if proche != n:
                    add(i, "info", f"{etiquette_l} : orthographe ? Désignation connue : « {noms[proche]} ».",
                        {"designation": noms[proche]})

        # doublons
        cle = (n, typ)
        if cle in vus:
            add(i, "alerte", f"{etiquette_l} : doublon de la ligne {vus[cle] + 1}.", None, "supprimer")
        else:
            vus[cle] = i

    if a_piece and not a_mo:
        add(None, "info", "Aucune ligne de main d'oeuvre dans ce devis.")
    if not any(str(l.get("designation", "")).strip() for l in lignes):
        add(None, "erreur", "Le devis est vide.")
    rang = {"erreur": 0, "alerte": 1, "info": 2}
    issues.sort(key=lambda x: (rang[x["niveau"]], -1 if x["ligne"] is None else x["ligne"]))
    return issues


# ---- D. Informations sur un client / véhicule / travaux déjà faits ---------

_INTERVALLES = [   # (libellé, motif, km, mois) : repères indicatifs, à adapter au véhicule
    ("Vidange huile + filtre", r"vidange|huile moteur|filtre a huile", 10000, 12),
    ("Filtre à air", r"filtre a air", 20000, 24),
    ("Filtre habitacle", r"filtre (?:d )?(?:habitacle|cabine|pollen|clim)", 20000, 24),
    ("Bougies", r"bougies?", 40000, 48),
    ("Kit distribution", r"distribution", 100000, 60),
    ("Courroie d'accessoires", r"courroie (?:d )?accessoires?", 100000, 60),
    ("Plaquettes de frein", r"plaquettes?", 40000, 36),
    ("Liquide de frein", r"liquide (?:de )?frein", 40000, 24),
    ("Liquide de refroidissement", r"refroidissement|antigel", 60000, 48),
    ("Filtre à carburant", r"filtre (?:a )?(?:carburant|gasoil|gazoil|essence)", 40000, 48),
    ("Amortisseurs", r"amortisseurs?", 80000, 72),
]
_MOTS_GENERIQUES = {"dernier", "derniere", "quand", "fait", "change", "changer", "remplace",
                    "remplacer", "deja", "travaux", "effectue", "effectuer", "fois", "combien",
                    "date", "client", "vehicule", "voiture", "qu", "quel", "quelle", "quels",
                    "quelles", "est", "ete", "avoir", "faire", "donne", "info", "information",
                    "montre", "afficher", "liste", "historique", "derniers", "dernieres"}


def _filtre_vehicule(client, immat):
    if immat:
        return "compact(d.immatriculation)=compact(?)", immat
    return "norm(d.client)=norm(?)", client


def travaux_historique(client="", immat=""):
    """Devis du véhicule (ou du client), du plus récent au plus ancien, avec leurs lignes."""
    if not (client or immat):
        return []
    cond, val = _filtre_vehicule(client, immat)
    with db() as c:
        devis = c.execute(f"SELECT d.* FROM devis d WHERE {cond} ORDER BY d.id DESC LIMIT 60",
                          (val,)).fetchall()
        par_devis = {}
        if devis:
            ids = [d["id"] for d in devis]
            marques = ",".join("?" * len(ids))
            for x in c.execute("SELECT devis_id, designation, quantite, prix_unitaire, type_ligne "
                               "FROM lignes_devis WHERE devis_id IN (%s) ORDER BY devis_id, numero" % marques, ids):
                par_devis.setdefault(x["devis_id"], []).append(
                    {"designation": x["designation"], "quantite": x["quantite"],
                     "prix_unitaire": x["prix_unitaire"], "type_ligne": x["type_ligne"]})
        res = []
        for d in devis:
            res.append({"id": d["id"], "date": d["date_devis"], "km": int(prix_nombre(d["kilometrage"]) or 0),
                        "vehicule": d["vehicule"], "immat": d["immatriculation"],
                        "total": d["total"], "statut": d["statut"],
                        "lignes": par_devis.get(d["id"], [])})
    return res


def _km_txt(n):
    return f"{int(n):,} km".replace(",", " ")


def _mois_depuis(date_fr):
    iso = iso_depuis_fr(date_fr)
    try:
        d = datetime.strptime(iso, "%Y-%m-%d")
    except Exception:
        return None
    nb = datetime.now()
    return max(0, (nb.year - d.year) * 12 + nb.month - d.month)


def entretien_a_prevoir(historique, km_actuel=0):
    """Pour chaque entretien courant : dernière fois faite et état (repères indicatifs)."""
    lignes = []
    for libelle, motif, km_int, mois_int in _INTERVALLES:
        trouve = next((d for d in historique
                       if any(re.search(motif, normaliser(l["designation"])) for l in d["lignes"])), None)
        if not trouve:
            lignes.append(f"- {libelle} : aucune trace dans l'historique (peut avoir été fait ailleurs).")
            continue
        ratios, detail = [], f"dernier : {trouve['date']}"
        if trouve["km"]:
            detail += ", " + _km_txt(trouve["km"])
        if km_actuel and trouve["km"] and km_actuel >= trouve["km"]:
            parcouru = km_actuel - trouve["km"]
            ratios.append(parcouru / km_int)
            detail += " ; " + _km_txt(parcouru) + " depuis"
        m = _mois_depuis(trouve["date"])
        if m is not None:
            ratios.append(m / mois_int)
            detail += f" ; il y a {m} mois"
        r = max(ratios) if ratios else 0
        etat = "A PRÉVOIR" if r >= 1 else ("bientôt" if r >= 0.8 else "ok")
        lignes.append(f"- {libelle} : {etat} ({detail}).")
    return lignes


def fiche_texte(client="", immat=""):
    """Résumé : contact, véhicules, dernier km, totaux, impayés."""
    hist = travaux_historique(client, immat)
    out = []
    with db() as c:
        cl = None
        if client:
            cl = c.execute("SELECT * FROM clients WHERE norm(nom)=norm(?) LIMIT 1", (client,)).fetchone()
        if not cl and immat:
            v = c.execute("SELECT client_id FROM vehicules WHERE compact(immatriculation)=compact(?) "
                          "ORDER BY id DESC LIMIT 1", (immat,)).fetchone()
            cl = c.execute("SELECT * FROM clients WHERE id=?", (v["client_id"],)).fetchone() if v else None
        if cl:
            out.append(f"CLIENT : {cl['nom']}")
            out.append(f"Téléphone : {cl['telephone'] or '-'} | E-mail : {cl['email'] or '-'}")
            vs = c.execute("SELECT * FROM vehicules WHERE client_id=? ORDER BY id DESC", (cl["id"],)).fetchall()
            if vs:
                out.append("Véhicules : " + " ; ".join(
                    f"{v['marque']} {v['immatriculation']}" + (f" ({v['moteur']})" if v["moteur"] else "")
                    for v in vs))
            cond, val = "norm(f.client)=norm(?)", cl["nom"]
        else:
            out.append("Aucune fiche client enregistrée pour cette saisie.")
            cond, val = ("compact(f.immatriculation)=compact(?)", immat) if immat else \
                        ("norm(f.client)=norm(?)", client)
        fac = c.execute(f"SELECT COUNT(*) AS nb, COALESCE(SUM(f.total),0) AS total, "
                        f"COALESCE(SUM({RESTE}),0) AS reste FROM factures f WHERE {cond}", (val,)).fetchone()
    km_d = next((d for d in hist if d["km"]), None)
    out.append(f"Devis enregistrés : {len(hist)}" + (f" | dernier : {hist[0]['date']}" if hist else ""))
    if km_d:
        out.append(f"Dernier kilométrage connu : {_km_txt(km_d['km'])} ({km_d['vehicule']}, {km_d['date']})")
    out.append(f"Factures : {fac['nb']} pour {prix_affiche(fac['total'])} | reste à payer : "
               f"{prix_affiche(max(0, fac['reste']))}")
    return "\n".join(out)


def _travaux_correspondant(question, historique):
    mots = _mots_cle(question) - _MOTS_GENERIQUES
    mots = {m for m in mots if not m.isdigit() and len(m) > 2}
    if not mots:
        return mots, []
    trouves = []
    for d in historique:
        for l in d["lignes"]:
            C = _mots_cle(l["designation"])
            if mots <= C or (len(mots) >= 3 and len(mots & C) / len(mots) >= 0.67):
                trouves.append((d, l))
    return mots, trouves


def repondre_hors_ligne(question, client="", immat="", km_actuel=0):
    """Réponse à une question sur le client / véhicule / travaux, d'après vos données."""
    q = normaliser(question)
    hist = travaux_historique(client, immat)
    parts = []
    if re.search(r"impay|doit|reste|solde|paiement|payer|paye", q):
        t = fiche_texte(client, immat)
        parts.append("\n".join(x for x in t.split("\n") if x.startswith("Factures")))
    if re.search(r"\bkm\b|kilometr", q):
        kms = [f"{d['date']} : {_km_txt(d['km'])} ({d['vehicule']})" for d in hist if d["km"]][:5]
        parts.append("Kilométrages relevés :\n" + ("\n".join(kms) if kms else "aucun kilométrage enregistré."))
    if re.search(r"telephone|\btel\b|numero|mail|contact|adresse", q):
        parts.append("\n".join(x for x in fiche_texte(client, immat).split("\n")[:2]))
    if re.search(r"vehicule|voiture|immat|moteur", q) and not re.search(r"travaux|change|remplac", q):
        parts.append("\n".join(x for x in fiche_texte(client, immat).split("\n") if x.startswith("Véhicules")))
    if re.search(r"prevoir|entretien|conseil|prochain|a faire|quoi faire", q):
        km_n = km_actuel or next((d["km"] for d in hist if d["km"]), 0)
        parts.append("Entretien (repères indicatifs, selon km " + (_km_txt(km_n)[:-3] if km_n else "inconnu")
                     + ") :\n" + "\n".join(entretien_a_prevoir(hist, km_n)))
    mots, trouves = _travaux_correspondant(q, hist)
    if trouves:
        lignes = []
        for d, l in trouves[:12]:
            km_t = ", " + _km_txt(d["km"]) if d["km"] else ""
            lignes.append(f"- {d['date']}{km_t} (devis n°{d['id']}) : {l['designation']} "
                          f"x{nombre_txt(l['quantite'])} à {prix_affiche(l['prix_unitaire'])}")
        parts.append("Travaux trouvés :\n" + "\n".join(lignes))
    elif mots and not parts:
        parts.append("Aucun travail correspondant (« " + " ".join(sorted(mots)) + " ») dans l'historique de ce "
                     + ("véhicule." if immat else "client."))
    if not parts:
        parts.append(fiche_texte(client, immat))
    return "\n\n".join(p for p in parts if p)


def contexte_anonyme(client="", immat="", marque="", moteur="", km_actuel=0, limite=6000):
    """Historique prêt pour l'IA : ni nom, ni téléphone, ni e-mail, ni plaque, ni VIN."""
    hist = travaux_historique(client, immat)
    out = [f"Véhicule : {marque or 'inconnu'}" + (f", moteur {moteur}" if moteur else "")
           + (f", kilométrage actuel {km_actuel} km" if km_actuel else "")]
    for d in hist:
        trav = "; ".join(f"{l['designation']} x{nombre_txt(l['quantite'])} ({prix_affiche(l['prix_unitaire'])})"
                         for l in d["lignes"])
        out.append(f"- {d['date']}" + (f", {d['km']} km" if d["km"] else "") + f", {d['statut']} : {trav}")
        if sum(len(x) for x in out) > limite:
            break
    return "\n".join(out)[:limite]
# ---- ASSISTANT_V96_END



# ---- IA optionnelle (en ligne) -------------------------------------------
# L'IA aide à comprendre un texte, relire un devis et répondre à une question.
# Elle ne décide JAMAIS d'un prix : les prix viennent de votre historique.
# Jamais envoyés : nom, téléphone, e-mail, plaque, VIN du client.

IA_URL = "https://api.anthropic.com/v1/messages"
IA_SYSTEME = (
    "Tu aides un garage automobile de Madagascar à préparer un devis. "
    "On te donne une demande en langage libre (français, malgache ou mélange, "
    "avec abréviations et fautes). Découpe-la en lignes de devis. "
    "Réponds UNIQUEMENT par un tableau JSON, sans texte ni balises. "
    "Chaque élément : {\"type\": \"Pièce\" ou \"M.O.\", \"designation\": texte court "
    "et clair en français, \"quantite\": nombre}. "
    "M.O. = main d'oeuvre (travail), Pièce = pièce ou fourniture. "
    "N'invente AUCUN prix et n'ajoute aucune pièce non demandée. "
    "Si la demande est une prestation globale (révision totale ou complète, petite révision, "
    "entretien), développe-la en lignes standard d'un garage : huile moteur (5 L) et filtres "
    "huile/air/habitacle, bougies (essence) ou filtre à gasoil (diesel), kit distribution + pompe "
    "à eau si le kilométrage dépasse 100 000 km ou est inconnu, courroie d'accessoires, liquides "
    "de refroidissement et de frein, plaquettes avant, puis la main d'oeuvre correspondante. "
    "Ignore dans la phrase tout ce qui concerne le client ou l'identité du véhicule. "
    "Utilise des désignations courtes et classiques (ex. « Filtre à huile », « Bougies d'allumage »). "
    "Ajoute si utile un champ \"note\" très court (ex. « à vérifier avec le carnet »). "
    "Maximum 30 lignes."
)
IA_SYSTEME_CONTROLE = (
    "Tu relis un devis de garage automobile (Madagascar). On te donne les lignes (index i, type, "
    "désignation, quantité, prix) et, quand elles existent, des prix de référence tirés de "
    "l'historique du garage. Cherche : fautes dans les désignations, quantités illogiques pour la "
    "pièce ou le moteur (ex. 8 litres d'huile pour une citadine), lignes incohérentes avec le "
    "travail, pièces ou main d'oeuvre probablement oubliées (ex. joint de vidange, remplacement "
    "de la courroie avec la pompe à eau). Tu ne proposes JAMAIS de prix. "
    "Réponds UNIQUEMENT par un tableau JSON. Chaque élément : "
    "{\"ligne\": index ou null, \"message\": phrase courte en français, "
    "\"correction\": {\"designation\"?, \"quantite\"?, \"type\"?} ou null, "
    "\"ajout\": {\"type\", \"designation\", \"quantite\"} ou null}. "
    "Ne répète pas les anomalies déjà listées. Maximum 12 éléments. Si tout est correct : []."
)
IA_SYSTEME_QUESTION = (
    "Tu es l'assistant d'un garage automobile à Madagascar. Réponds en français, de façon brève et "
    "concrète, UNIQUEMENT à partir de l'historique fourni. Si l'information n'y figure pas, dis-le "
    "clairement. Tu peux suggérer des entretiens à prévoir selon le kilométrage et les travaux "
    "passés, en précisant que ce sont des suggestions à vérifier. N'invente aucun prix ni date."
)


def ia_disponible():
    return param("ia_active") == "Oui" and bool(param("ia_cle").strip())


def ia_historique_autorise():
    return ia_disponible() and param("ia_historique") == "Oui"


def _appel_ia(systeme, message, max_tokens=1500):
    """Appelle l'API et retourne le texte de la réponse. Lève RuntimeError avec un message clair."""
    if not ia_disponible():
        raise RuntimeError("IA désactivée : activez-la et saisissez la clé dans Paramètres.")
    corps = json.dumps({
        "model": param("ia_modele").strip() or "claude-haiku-5-5",
        "max_tokens": max_tokens,
        "system": systeme,
        "messages": [{"role": "user", "content": message}],
    }).encode("utf-8")
    req = urllib.request.Request(IA_URL, data=corps, method="POST", headers={
        "content-type": "application/json",
        "x-api-key": param("ia_cle").strip(),
        "anthropic-version": "2023-06-01",
    })
    try:
        with urllib.request.urlopen(req, timeout=40) as r:
            data = json.loads(r.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        if e.code in (401, 403):
            raise RuntimeError("Clé API refusée. Vérifiez-la dans Paramètres.")
        if e.code == 429:
            raise RuntimeError("Trop de demandes ou crédit épuisé. Réessayez plus tard.")
        raise RuntimeError(f"Erreur du service IA (code {e.code}).")
    except Exception as e:
        raise RuntimeError("Pas de connexion à l'IA : " + str(e))
    return "".join(b.get("text", "") for b in data.get("content", []) if b.get("type") == "text")


def _json_liste(brut):
    brut = re.sub(r"```(?:json)?", "", str(brut)).strip()
    debut, fin = brut.find("["), brut.rfind("]")
    if debut < 0 or fin < debut:
        raise RuntimeError("Réponse de l'IA illisible.")
    try:
        res = json.loads(brut[debut:fin + 1])
    except ValueError:
        raise RuntimeError("Réponse de l'IA illisible.")
    return [x for x in res if isinstance(x, dict)]


def _type_valide(t):
    return "M.O." if str(t or "").strip().lower() in ("m.o.", "mo", "m.o", "main d'oeuvre") else "Pièce"


def ia_analyser_demande(texte, vehicule="", details=""):
    """Structure le texte en lignes (type, désignation, quantité). Le texte est anonymisé."""
    message = ((f"Véhicule : {anonymiser_texte(vehicule)}\n" if vehicule else "")
               + (f"Détails : {anonymiser_texte(details)}\n" if details else "")
               + "Demande :\n" + anonymiser_texte(texte)[:3000])
    demandes = []
    for el in _json_liste(_appel_ia(IA_SYSTEME, message))[:30]:
        des = str(el.get("designation", "")).strip()[:120]
        if not des:
            continue
        q = prix_nombre(el.get("quantite", 1))
        demandes.append({"type": _type_valide(el.get("type")), "designation": des,
                         "quantite": q if q > 0 else 1.0, "prix": 0.0,
                         "source_prix": "À confirmer", "note": str(el.get("note", "")).strip()[:80]})
    return demandes


def suggerer_lignes_devis_ia(texte, vehicule="", km="", moteur=""):
    """IA pour comprendre la demande + historique local pour les prix."""
    details = ", ".join(x for x in (f"moteur {moteur}" if moteur else "",
                                    f"{km} km" if km else "") if x)
    return appliquer_prix_historique(ia_analyser_demande(texte, vehicule, details), vehicule)


def ia_controler_devis(lignes, vehicule="", km=0, moteur="", deja=None):
    """Relecture du devis par l'IA. Retourne des anomalies au même format que controler_devis.
    Garde-fous : aucune correction de prix venant de l'IA ; les ajouts sont chiffrés par l'historique."""
    if not ia_disponible():
        raise RuntimeError("IA désactivée ou clé API manquante.")
    cands = _candidats_prix()
    donnees = []
    for i, l in enumerate(lignes[:60]):
        des = str(l.get("designation", ""))[:120]
        ref = prix_reference(des, vehicule, cands) if des else None     # références LOCALES, sur l'original
        donnees.append({"i": i, "type": str(l.get("type", ""))[:20], "designation": anonymiser_texte(des),
                        "quantite": prix_nombre(l.get("quantite", 0)), "prix": prix_nombre(l.get("prix", 0)),
                        "prix_reference": ref["mediane"] if ref else None,
                        "nb_references": ref["n"] if ref else 0})
    deja = [anonymiser_texte(x)[:200] for x in (deja or [])[:30]]
    message = (f"Véhicule : {anonymiser_texte(vehicule) or 'inconnu'}"
               + (f", moteur {anonymiser_texte(moteur)}" if moteur else "")
               + (f", {int(prix_nombre(km))} km" if prix_nombre(km) else "")
               + "\nLignes :\n" + json.dumps(donnees, ensure_ascii=False)
               + "\nAnomalies déjà listées (ne pas répéter) :\n" + "\n".join(deja)[:1500])
    issues = []
    for el in _json_liste(_appel_ia(IA_SYSTEME_CONTROLE, message, 1500))[:12]:
        msg = str(el.get("message", "")).strip()[:200]
        if not msg:
            continue
        i = el.get("ligne")
        i = i if isinstance(i, int) and 0 <= i < len(lignes) else None
        corr = {}
        c0 = el.get("correction") if isinstance(el.get("correction"), dict) else {}
        if "designation" in c0 and str(c0["designation"]).strip():
            corr["designation"] = str(c0["designation"]).strip()[:120]
        if "quantite" in c0 and prix_nombre(c0["quantite"]) > 0:
            corr["quantite"] = prix_nombre(c0["quantite"])
        if "type" in c0:
            corr["type"] = _type_valide(c0["type"])
        aj = el.get("ajout") if isinstance(el.get("ajout"), dict) else None
        if aj and str(aj.get("designation", "")).strip():
            ligne = {"type": _type_valide(aj.get("type")), "designation": str(aj["designation"]).strip()[:120],
                     "quantite": prix_nombre(aj.get("quantite", 1)) or 1.0, "prix": 0.0}
            ligne = appliquer_prix_historique([ligne], vehicule)[0]
            issues.append({"ligne": None, "niveau": "info", "message": "IA : " + msg,
                           "action": "ajouter", "correction": {k: ligne[k] for k in ("type", "designation", "quantite", "prix")}})
        elif i is not None and corr:
            issues.append({"ligne": i, "niveau": "info", "message": "IA : " + msg,
                           "action": "modifier", "correction": corr})
        else:
            issues.append({"ligne": i, "niveau": "info", "message": "IA : " + msg,
                           "action": "modifier", "correction": None})
    return issues


def ia_repondre(question, contexte):
    """Réponse libre de l'IA d'après l'historique ANONYMISÉ (voir contexte_anonyme)."""
    if not ia_historique_autorise():
        raise RuntimeError("L'IA n'est pas autorisée à lire l'historique (Paramètres).")
    return _appel_ia(IA_SYSTEME_QUESTION, f"Historique du véhicule :\n{contexte}\n\nQuestion : "
                     f"{anonymiser_texte(question)[:500]}", 900).strip()




# ---- Ponts : mêmes noms que la V9.10, moteur plus intelligent --------------

def meilleure_correspondance(valeur, candidats, seuil=0.84):
    """(candidat, score) le plus proche parmi [{'id','nom'}], ou (None, 0) si flou ou ambigu."""
    cible = _nom_sans_titre(valeur)
    if len(cible) < 3:
        return None, 0.0
    notes = []
    for cand in candidats:
        n = _nom_sans_titre(cand["nom"])
        s = difflib.SequenceMatcher(None, cible, n).ratio()
        if len(cible) >= 4 and any(t.startswith(cible) for t in n.split()):
            s = max(s, 0.85)
        if (re.fullmatch(r"[a-z0-9]{5,9}", cible) and re.search(r"\d", cible) and re.search(r"[a-z]", cible)
                and abs(len(cible) - len(n)) <= 1 and s >= 0.84):
            s = max(s, 0.9)               # plaque : une seule faute de frappe
        notes.append((s, cand))
    notes.sort(key=lambda x: -x[0])
    if not notes or notes[0][0] < seuil:
        return None, 0.0
    if len(notes) > 1 and notes[1][0] >= notes[0][0] - 0.02 and \
            _nom_sans_titre(notes[1][1]["nom"]) != _nom_sans_titre(notes[0][1]["nom"]):
        return None, 0.0            # deux candidats aussi proches : jamais de choix ambigu
    return notes[0][1], notes[0][0]


def proposer_correction_email(adresse):
    return corriger_email(adresse)


def cle_plaque(texte):
    return compacter(texte)


def _analyse_devis(lignes, vehicule="", km=0):
    return controler_devis(lignes, vehicule, int(prix_nombre(km) or 0))


def controler_devis_local(lignes, vehicule="", km=0):
    """Alertes du contrôle qui n'ont pas de bouton APPLIQUER (doublons, quantités suspectes...)."""
    res = []
    for it in _analyse_devis(lignes, vehicule, km):
        if it["action"] == "modifier" and it.get("correction"):
            continue                       # proposée avec bouton dans proposer_corrections_lignes
        res.append({"niveau": it["niveau"], "message": it["message"]})
    return res


def proposer_corrections_lignes(lignes, vehicule="", km=0):
    """Corrections fondées sur l'historique : prix, quantité, type, désignation.
    Rien n'est appliqué ici : l'utilisateur clique."""
    champs_ligne = {"prix": "prix", "quantite": "quantite", "type": "type", "designation": "designation"}
    par_ligne = {}
    for it in _analyse_devis(lignes, vehicule, km):
        corr = it.get("correction") or {}
        if it["action"] != "modifier" or not corr or it["ligne"] is None:
            continue
        for champ, valeur in corr.items():
            if champ in champs_ligne:
                par_ligne.setdefault(it["ligne"], []).append({
                    "champ": champ, "actuel": lignes[it["ligne"]].get(champs_ligne[champ]),
                    "propose": valeur, "raison": it["detail"], "references": it.get("references", 0),
                    "niveau": it["niveau"]})
    return [{"index": i, "designation": str(lignes[i].get("designation", "")).strip(), "suggestions": s}
            for i, s in sorted(par_ligne.items())]


def repondre_question_historique(question, client="", immat="", km_actuel=0):
    """Réponse locale d'après vos données : travaux, km, impayés, contact, entretien à prévoir."""
    if not (client or immat):
        return "Saisissez un nom de client ou une immatriculation."
    if not travaux_historique(client, immat) and not re.search(r"telephone|\btel\b|mail|contact", normaliser(question)):
        return ("Aucun historique enregistré pour cette recherche. Un travail effectué ailleurs "
                "peut ne pas apparaître ici.")
    return repondre_hors_ligne(question, client, immat, km_actuel)



def etiquette_multi(texte, taille=11, couleur=GRIS_TEXTE):
    """Texte sur plusieurs lignes, hauteur automatique (etiquette() coupe le texte long)."""
    lbl = Label(text=str(texte), font_size=sp(taille), color=couleur, halign="left", valign="top",
                size_hint_y=None)
    lbl.bind(width=lambda i, w: setattr(i, "text_size", (max(10, w - dp(6)), None)))
    lbl.bind(texture_size=lambda i, ts: setattr(i, "height", max(dp(24), ts[1] + dp(8))))
    return lbl


def auditer_prix_base(limite=120):
    """Repère les montants suspects et totaux incohérents sans modifier la base.

    Les comparaisons reposent sur les lignes historiques de désignation identique.
    Un montant atypique est seulement proposé à vérification humaine.
    """
    avec_prix = []
    anomalies = []
    with db() as c:
        for r in c.execute("""SELECT 'DEVIS' AS source, l.id AS ligne_id, l.devis_id AS doc_id,
                    d.date_devis AS date_doc, l.designation, l.quantite, l.prix_unitaire AS prix,
                    l.total, d.vehicule AS vehicule
                    FROM lignes_devis l JOIN devis d ON d.id=l.devis_id
                    WHERE COALESCE(l.prix_unitaire,0)>0 ORDER BY l.id DESC LIMIT 10000""").fetchall():
            avec_prix.append(dict(r))
        for r in c.execute("""SELECT 'FACTURE' AS source, l.id AS ligne_id, l.facture_id AS doc_id,
                    f.date_facture AS date_doc, l.designation, l.quantite, l.prix_unitaire AS prix,
                    l.total, f.vehicule AS vehicule
                    FROM lignes_facture l JOIN factures f ON f.id=l.facture_id
                    WHERE COALESCE(l.prix_unitaire,0)>0 ORDER BY l.id DESC LIMIT 10000""").fetchall():
            avec_prix.append(dict(r))
        for r in c.execute("""SELECT id, designation, prix, date_prix, marque FROM historique_prix
                    WHERE COALESCE(prix,0)>0 ORDER BY id DESC LIMIT 10000""").fetchall():
            avec_prix.append({"source":"HISTORIQUE", "ligne_id":r["id"], "doc_id":"-",
                              "date_doc":r["date_prix"], "designation":r["designation"],
                              "quantite":1, "prix":r["prix"], "total":r["prix"], "vehicule":r["marque"]})

    groupes = {}
    for r in avec_prix:
        cle = normaliser(r.get("designation", ""))
        val = prix_nombre(r.get("prix"))
        if cle and val > 0:
            groupes.setdefault(cle, []).append(val)
    for liste in groupes.values():   # tri fait UNE fois par groupe (et non à chaque ligne)
        liste.sort()

    # Comparer chaque ligne aux autres valeurs de même désignation, sans elle-même.
    for r in avec_prix:
        des = str(r.get("designation") or "").strip()
        prix = prix_nombre(r.get("prix"))
        qte = prix_nombre(r.get("quantite", 1)) or 1
        total = prix_nombre(r.get("total", 0))
        cle = normaliser(des)
        refs = groupes.get(cle, [])
        if prix > 0 and len(refs) >= 2:
            # refs est déjà trié ; on « retire » une occurrence du prix courant par indice,
            # sans copier la liste, pour que la ligne ne se valide pas elle-même.
            pos = bisect.bisect_left(refs, prix)
            if pos < len(refs) and refs[pos] == prix:
                n_autres = len(refs) - 1
                if n_autres:
                    k = (n_autres - 1) // 2
                    repere = refs[k + 1] if k >= pos else refs[k]
                else:
                    repere = None
            else:
                n_autres = len(refs)
                repere = refs[(n_autres - 1) // 2] if n_autres else None
            if repere is not None:
                # Avec seulement deux valeurs très différentes, on signale la valeur haute,
                # mais on n'accuse pas la valeur basse : elle peut être la bonne.
                suspect_haut = repere > 0 and prix >= repere * 4
                suspect_bas = len(refs) >= 3 and repere > 0 and prix <= repere * 0.25
                if suspect_haut or suspect_bas:
                    anomalies.append({"niveau":"alerte", "message":
                        f"{r['source']} #{r['doc_id']} ({r.get('date_doc') or 'date inconnue'}) — {des}: "
                        f"prix enregistré {prix_affiche(prix)}, repère d'autres enregistrements {prix_affiche(repere)}. "
                        "Vérifier une possible concaténation ou erreur de saisie"
                        + (" (écart proche de x10 : un zéro en trop ou manquant ?)"
                           if repere > 0 and (8 <= prix / repere <= 12 or 0.08 <= prix / repere <= 0.125) else "")
                        + "; aucune correction appliquée."})
        calcule = qte * prix
        if total > 0 and calcule > 0 and abs(total - calcule) > max(2, calcule * 0.01):
            anomalies.append({"niveau":"alerte", "message":
                f"{r['source']} #{r['doc_id']} — {des}: total de ligne {prix_affiche(total)} différent de quantité × prix "
                f"({nombre_txt(qte)} × {prix_affiche(prix)} = {prix_affiche(calcule)}). Vérifier l'enregistrement."})
        if len(anomalies) >= limite:
            break
    return anomalies[:limite]


def texte_audit_prix_base():
    anomalies = auditer_prix_base()
    if not anomalies:
        return ("Audit terminé : aucune anomalie évidente détectée dans les prix comparables.\n"
                "Cela ne garantit pas que chaque montant est exact. Aucune donnée n'a été modifiée.")
    return (f"{len(anomalies)} anomalie(s) potentielle(s) détectée(s).\n"
            "Les montants sont uniquement signalés : aucune correction automatique.\n\n"
            + "\n\n".join("• " + x["message"] for x in anomalies))


def fiche_client_vehicule(client="", immat=""):
    """Fiche locale sans mélanger les kilométrages de plusieurs véhicules d'un client."""
    lignes = []
    with db() as c:
        cl = None
        if immat:
            v0 = c.execute("SELECT * FROM vehicules WHERE compact(immatriculation)=compact(?) ORDER BY id DESC LIMIT 1", (immat,)).fetchone()
            if v0 and v0["client_id"]:
                cl = c.execute("SELECT * FROM clients WHERE id=?", (v0["client_id"],)).fetchone()
        else:
            v0 = None
        if not cl and client:
            cl = c.execute("SELECT * FROM clients WHERE norm(nom)=norm(?) ORDER BY id DESC LIMIT 1", (client,)).fetchone()
        if cl:
            lignes += ["CLIENT", "Nom : " + str(cl["nom"] or "-"),
                       "Téléphone : " + str(cl["telephone"] or "-"),
                       "E-mail : " + str(cl["email"] or "-")]
        vehicules = []
        if immat:
            if v0:
                vehicules = [v0]
        elif client:
            # Inclure aussi les anciens doublons de fiches client portant le même nom normalisé.
            vehicules = c.execute("SELECT v.* FROM vehicules v JOIN clients c ON c.id=v.client_id WHERE norm(c.nom)=norm(?) ORDER BY v.id DESC", (client,)).fetchall()
        if vehicules:
            lignes += ["", "VÉHICULE(S)"]
            for v in vehicules:
                lignes += ["Marque / modèle : " + str(v["marque"] or "") + " " + str(v["modele"] or ""),
                           "Immatriculation : " + str(v["immatriculation"] or "-"),
                           "Moteur : " + str(v["moteur"] or "-"),
                           "VIN : " + str(v["vin"] or "-"),
                           "Kilométrage enregistré pour ce véhicule : " + str(v["kilometrage"] or "-") , ""]
        if immat:
            devis = c.execute("SELECT * FROM devis WHERE compact(immatriculation)=compact(?) ORDER BY id DESC LIMIT 25", (immat,)).fetchall()
        elif client:
            devis = c.execute("SELECT * FROM devis WHERE norm(client)=norm(?) ORDER BY id DESC LIMIT 25", (client,)).fetchall()
        else:
            devis = []
        lignes += ["HISTORIQUE DES DEVIS / TRAVAUX"]
        if not devis:
            lignes.append("Aucun devis trouvé pour cette recherche.")
        for d in devis:
            travaux = c.execute("SELECT designation, quantite FROM lignes_devis WHERE devis_id=? ORDER BY numero", (d["id"],)).fetchall()
            noms = "; ".join(str(t["designation"]) + (" x" + nombre_txt(t["quantite"]) if t["quantite"] != 1 else "") for t in travaux)
            lignes.append(f"{d['date_devis']} | {d['vehicule']} | {d['immatriculation']} | {d['statut']} | {prix_affiche(d['total'])}\n  {noms or '-'}")
    return "\n".join(lignes) if lignes else "Aucune fiche trouvée."



def sauver_devis(d, lignes, devis_id=None, taux=0.0):
    """Crée ou met à jour un devis. Une modification incrémente la version."""
    aujourdhui = datetime.now().strftime("%d/%m/%Y")
    if not str(d.get("client", "")).strip():
        raise ValueError("Le nom du client est obligatoire.")
    if not compacter(d.get("immat", "")):
        raise ValueError("L'immatriculation du véhicule est obligatoire.")
    if not email_valide(d.get("email", "")):
        raise ValueError("L'adresse e-mail du client n'est pas valide.")
    if taux < 0 or taux > 100:
        raise ValueError("Le taux de TVA doit être compris entre 0 et 100 %. ")
    lignes_corrigees = []
    for index, ligne in enumerate(lignes, 1):
        designation = str(ligne.get("designation", "")).strip()
        quantite = prix_nombre(ligne.get("quantite", 0))
        prix = prix_nombre(ligne.get("prix", 0))
        type_ligne = str(ligne.get("type", "Pièce"))
        if not designation:
            raise ValueError(f"La désignation de la ligne {index} est obligatoire.")
        if quantite <= 0:
            raise ValueError(f"La quantité de la ligne {index} doit être supérieure à zéro.")
        if prix < 0:
            raise ValueError(f"Le prix de la ligne {index} ne peut pas être négatif.")
        if type_ligne not in ("Pièce", "M.O."):
            type_ligne = "Pièce"
        lignes_corrigees.append({"type": type_ligne, "designation": designation,
                                 "quantite": quantite, "prix": prix, "total": quantite * prix})
    if not lignes_corrigees:
        raise ValueError("Ajoutez au moins une ligne au devis.")
    lignes = lignes_corrigees
    ttc = totaux(lignes, taux)["ttc"]
    with db() as c:
        r = c.execute("SELECT id FROM clients WHERE norm(trim(nom))=norm(trim(?)) LIMIT 1", (d["client"],)).fetchone()
        if r:
            client_id = r["id"]
            c.execute("UPDATE clients SET telephone=COALESCE(NULLIF(?, ''), telephone), "
                      "email=COALESCE(NULLIF(?, ''), email) WHERE id=?",
                      (d["telephone"], d["email"], client_id))
        else:
            client_id = c.execute("INSERT INTO clients (nom, telephone, email) VALUES (?,?,?)",
                                  (d["client"], d["telephone"], d["email"])).lastrowid

        r = c.execute("SELECT id FROM vehicules WHERE client_id=? AND compact(immatriculation)=compact(?)",
                      (client_id, d["immat"])).fetchone()
        if r:  # plus de doublons de véhicule à chaque devis
            c.execute("UPDATE vehicules SET marque=?, kilometrage=?, moteur=?, vin=? WHERE id=?",
                      (d["vehicule"], d["km"], d["moteur"], d.get("vin", ""), r["id"]))
        else:
            c.execute("INSERT INTO vehicules (client_id, marque, immatriculation, kilometrage, moteur, vin) "
                      "VALUES (?,?,?,?,?,?)", (client_id, d["vehicule"], d["immat"], d["km"], d["moteur"],
                                               d.get("vin", "")))

        if devis_id is None:
            version = 1
            devis_id = c.execute(
                "INSERT INTO devis (client, vehicule, immatriculation, date_devis, kilometrage, "
                "total, statut, version, tva_taux) VALUES (?,?,?,?,?,?,?,?,?)",
                (d["client"], d["vehicule"], d["immat"], aujourdhui, d["km"], ttc,
                 "En attente", 1, taux)).lastrowid
        else:
            row = c.execute("SELECT version, statut FROM devis WHERE id=?", (devis_id,)).fetchone()
            if not row:
                raise ValueError("Devis introuvable.")
            if row["statut"] == "Facturé":
                raise ValueError("Ce devis est déjà facturé : il ne peut plus être modifié.")
            version = int(row["version"] or 1) + 1
            c.execute("UPDATE devis SET client=?, vehicule=?, immatriculation=?, kilometrage=?, "
                      "total=?, version=?, tva_taux=? WHERE id=?",
                      (d["client"], d["vehicule"], d["immat"], d["km"], ttc, version, taux, devis_id))
            c.execute("DELETE FROM lignes_devis WHERE devis_id=?", (devis_id,))

        for idx, l in enumerate(lignes, 1):
            c.execute("INSERT INTO lignes_devis (devis_id, numero, type_ligne, designation, quantite, "
                      "prix_unitaire, total) VALUES (?,?,?,?,?,?,?)",
                      (devis_id, idx, l["type"], l["designation"], l["quantite"], l["prix"], l["total"]))
            if l["prix"] > 0:  # alimente la mémoire des prix
                deja = c.execute("SELECT 1 FROM historique_prix WHERE designation=? AND marque=? "
                                 "AND prix=? AND date_prix=?",
                                 (l["designation"], d["vehicule"], l["prix"], aujourdhui)).fetchone()
                if not deja:
                    c.execute("INSERT INTO historique_prix (marque, modele, designation, prix, date_prix) "
                              "VALUES (?,?,?,?,?)", (d["vehicule"], "", l["designation"], l["prix"], aujourdhui))
    return devis_id, version


def facturer_devis(devis_id):
    with db() as c:
        d = c.execute("SELECT * FROM devis WHERE id=?", (devis_id,)).fetchone()
        if not d:
            raise ValueError("Devis introuvable.")
        if c.execute("SELECT 1 FROM factures WHERE devis_id=?", (devis_id,)).fetchone():
            raise ValueError("Ce devis est déjà facturé.")
        # Contrôles avant émission : aucune facture vide ou avec lignes manifestement invalides.
        lignes_src = c.execute("SELECT designation, quantite, prix_unitaire, total FROM lignes_devis WHERE devis_id=? ORDER BY numero", (devis_id,)).fetchall()
        if not str(d["client"] or "").strip() or not str(d["immatriculation"] or "").strip():
            raise ValueError("Facturation impossible : client ou immatriculation manquant dans le devis.")
        if not lignes_src:
            raise ValueError("Facturation impossible : ce devis ne contient aucune ligne.")
        somme_ht = 0.0
        for no, ligne in enumerate(lignes_src, 1):
            if not str(ligne["designation"] or "").strip():
                raise ValueError(f"Facturation impossible : désignation vide à la ligne {no}.")
            q = prix_nombre(ligne["quantite"])
            pu = prix_nombre(ligne["prix_unitaire"])
            total_ligne = prix_nombre(ligne["total"])
            if q <= 0 or pu < 0:
                raise ValueError(f"Facturation impossible : quantité ou prix invalide à la ligne {no}.")
            if abs(total_ligne - q * pu) > 1.0:
                raise ValueError(f"Facturation impossible : total incohérent à la ligne {no}. Réouvrez le devis et vérifiez-le.")
            somme_ht += total_ligne
        taux_tva = prix_nombre(d["tva_taux"] or 0)
        total_attendu = round(somme_ht * (1 + taux_tva / 100.0))
        if abs(prix_nombre(d["total"]) - total_attendu) > 1.0:
            raise ValueError("Facturation impossible : le total du devis ne correspond pas à ses lignes et à la TVA. Réouvrez et vérifiez le devis avant de facturer.")
        fid = c.execute(
            "INSERT INTO factures (devis_id, client, vehicule, immatriculation, date_facture, total, "
            "tva_taux, paye) VALUES (?,?,?,?,?,?,?,0)",
            (devis_id, d["client"], d["vehicule"], d["immatriculation"],
             datetime.now().strftime("%d/%m/%Y"), d["total"], d["tva_taux"] or 0)).lastrowid
        c.execute("INSERT INTO lignes_facture (facture_id, numero, type_ligne, designation, quantite, "
                  "prix_unitaire, total) SELECT ?, numero, type_ligne, designation, quantite, "
                  "prix_unitaire, total FROM lignes_devis WHERE devis_id=?", (fid, devis_id))
        c.execute("UPDATE devis SET statut='Facturé' WHERE id=?", (devis_id,))
    return fid


def stats():
    mois = datetime.now().strftime("%Y-%m")
    with db() as c:
        ca = c.execute("SELECT COALESCE(SUM(montant),0) FROM paiements WHERE annule=0 AND date_iso LIKE ?",
                       (mois + "%",)).fetchone()[0]
        somme, nb = c.execute(
            "SELECT COALESCE(SUM(reste),0), COUNT(*) FROM ("
            "SELECT f.total - COALESCE((SELECT SUM(montant) FROM paiements p "
            "WHERE p.facture_id=f.id AND p.annule=0),0) AS reste FROM factures f) WHERE reste > 0.5").fetchone()
        att = c.execute("SELECT COUNT(*) FROM devis WHERE statut != 'Facturé'").fetchone()[0]
    return ca, somme, nb, att


# ============================================================
# PDF
# ============================================================

def generer_pdf(type_doc, doc_id, doc):
    if not HAS_REPORTLAB:
        return None
    lignes, taux = doc["lignes"], doc["tva_taux"]
    t = totaux(lignes, taux)
    numero = numero_doc("DEV" if type_doc == "Devis" else "FAC", doc_id, doc["date"])
    rev = f"_rev{doc['version']}" if type_doc == "Devis" and doc["version"] > 1 else ""
    chemin = os.path.join(DOSSIER_PDF, f"{numero}_{nom_fichier_sur(doc['immatriculation'])}{rev}.pdf")

    c = canvas.Canvas(chemin, pagesize=A4)
    L, R = 40, 555
    page = [1]

    def entete():
        c.setFont("Helvetica-Bold", 14)
        c.drawString(L, 800, param("garage_nom"))
        c.setFont("Helvetica", 9)
        for i, cle in enumerate(("garage_adresse", "garage_nif", "garage_contact")):
            c.drawString(L, 786 - 13 * i, param(cle))
        c.setFont("Helvetica-Bold", 12)
        suffixe = f" - révision {doc['version']}" if type_doc == "Devis" and doc["version"] > 1 else ""
        c.drawString(L, 730, f"{type_doc.upper()} N° {numero}{suffixe}")
        c.setFont("Helvetica", 10)
        c.drawString(L, 715, f"Date : {doc['date']}")
        c.drawString(L, 700, f"Immatriculation du véhicule : {doc['immatriculation']}")
        c.drawString(L, 685, f"Kilométrage : {doc['km']}")
        c.drawString(L, 670, f"Véhicule : {doc['vehicule']}")
        c.setFont("Helvetica-Bold", 11)
        c.drawString(350, 730, f"Doit à : {str(doc['client'])[:32]}")
        if doc.get("vin"):
            c.setFont("Helvetica", 9)
            c.drawString(350, 700, f"VIN : {doc['vin']}")

    def entete_tableau(y):
        c.setFont("Helvetica-Bold", 9)
        c.drawString(L, y, "N°")
        c.drawString(70, y, "Désignation des travaux ou pièces")
        c.drawRightString(380, y, "Qté")
        c.drawRightString(460, y, "PU (Ar)")
        c.drawRightString(R, y, "Total (Ar)")
        c.setLineWidth(0.5)
        c.line(L, y - 5, R, y - 5)
        return y - 20

    def pied():
        c.setFont("Helvetica", 8)
        c.drawCentredString(297, 25, f"{param('garage_nom')} - Page {page[0]}")

    def nouvelle_page():
        pied()
        c.showPage()
        page[0] += 1
        entete()
        return entete_tableau(640)

    entete()
    y = entete_tableau(640)
    for i, l in enumerate(lignes, 1):
        morceaux = simpleSplit(str(l["designation"]), "Helvetica", 8, 270) or [""]
        if y - 11 * len(morceaux) < 60:
            y = nouvelle_page()
        c.setFont("Helvetica", 8)
        c.drawString(L, y, str(i))
        for k, m in enumerate(morceaux):  # la désignation n'est plus tronquée
            c.drawString(70, y - 11 * k, m)
        c.drawRightString(380, y, nombre_txt(l["quantite"]))
        c.drawRightString(460, y, prix_affiche(l["prix"]))
        c.drawRightString(R, y, prix_affiche(l["total"]))
        y -= 11 * len(morceaux) + 4

    if y < 190:  # le bloc des totaux ne doit jamais sortir de la page
        y = nouvelle_page()
    c.line(L, y, R, y)
    y -= 16
    c.setFont("Helvetica", 9)
    detail = [("Pièces", t["pieces"]), ("Main-d'œuvre", t["mo"])]
    if taux:
        detail += [("Total HT", t["ht"]), (f"TVA {taux:g} %", t["tva"])]
    for lib, val in detail:
        c.drawString(380, y, lib)
        c.drawRightString(R, y, prix_affiche(val))
        y -= 13
    c.setFont("Helvetica-Bold", 12)
    c.drawString(380, y - 4, "TOTAL TTC" if taux else "TOTAL")
    c.drawRightString(R, y - 4, prix_affiche(t["ttc"]))
    y -= 40

    c.setFont("Helvetica", 9)
    if type_doc == "Devis":
        c.drawString(L, y, "Devis valable 30 jours.")
        c.drawString(L, y - 30, "Bon pour accord (date et signature du client) :")
        c.line(L, y - 70, 260, y - 70)
    else:
        c.drawString(L, y, "Merci de votre confiance.")
    pied()
    c.save()
    return chemin


def regenerer_pdf(type_doc, doc_id):
    doc = charger_document(type_doc, doc_id)
    return generer_pdf(type_doc, doc_id, doc), doc


def generer_pdf_recu_avance(fid, paiement_id):
    """Crée un reçu PDF client pour une avance/un paiement réellement enregistré."""
    if not HAS_REPORTLAB:
        raise RuntimeError("La bibliothèque ReportLab est nécessaire pour générer le reçu PDF.")
    with db() as c:
        f = c.execute("SELECT * FROM factures WHERE id=?", (fid,)).fetchone()
        p = c.execute("SELECT * FROM paiements WHERE id=? AND facture_id=? AND annule=0",
                      (paiement_id, fid)).fetchone()
        total_paye = c.execute("SELECT COALESCE(SUM(montant),0) FROM paiements WHERE facture_id=? AND annule=0",
                               (fid,)).fetchone()[0]
    if not f or not p:
        raise ValueError("Facture ou paiement introuvable pour créer le reçu.")
    reste = max(0, float(f["total"] or 0) - float(total_paye or 0))
    numero = numero_doc("FAC", fid, f["date_facture"])
    recu = "REC-{}-{:04d}".format(datetime.strptime(p["date_iso"], "%Y-%m-%d").year, int(paiement_id))
    chemin = os.path.join(DOSSIER_PDF, "{}_{}.pdf".format(recu, nom_fichier_sur(f["immatriculation"])))
    c = canvas.Canvas(chemin, pagesize=A4)
    c.setTitle("Reçu de paiement {}".format(recu))
    c.setFont("Helvetica-Bold", 15); c.drawString(42, 800, param("garage_nom"))
    c.setFont("Helvetica", 9)
    y=782
    for cle in ("garage_adresse", "garage_nif", "garage_contact"):
        c.drawString(42, y, param(cle)); y -= 13
    c.setFont("Helvetica-Bold", 16); c.drawString(42, 715, "REÇU D'AVANCE / DE PAIEMENT")
    c.setFont("Helvetica-Bold", 11); c.drawString(42, 685, "Reçu N° : " + recu)
    c.setFont("Helvetica", 10)
    infos=[("Date du paiement", fr_depuis_iso(p["date_iso"])), ("Client", f["client"] or "-"),
           ("Facture concernée", numero), ("Véhicule", "{} - {}".format(f["vehicule"] or "", f["immatriculation"] or "")),
           ("Mode de paiement", p["mode"] or "-"), ("Référence de paiement", p["reference"] or "-"),
           ("Montant reçu", prix_affiche(p["montant"])),
           ("Total de la facture", prix_affiche(f["total"])), ("Total payé à ce jour", prix_affiche(total_paye)),
           ("Reste à payer", prix_affiche(reste))]
    y=650
    for lib,val in infos:
        c.setFont("Helvetica-Bold", 10); c.drawString(48,y,lib+" :")
        c.setFont("Helvetica", 10)
        c.drawString(205,y,str(val)[:65]); y-=28
    c.setLineWidth(.8); c.line(42,y-8,550,y-8)
    c.setFont("Helvetica",9)
    c.drawString(42,y-32,"Ce document confirme la réception du montant indiqué pour la facture ci-dessus.")
    c.drawString(42,y-48,"Merci de votre confiance.")
    c.drawString(42,70,"Signature / cachet : __________________________________")
    c.save()
    return chemin


def generer_pdf_recap_factures():
    """Récapitulatif daté : toutes les factures encore dues et les avances encaissées depuis aujourd'hui."""
    if not HAS_REPORTLAB:
        raise RuntimeError("La bibliothèque ReportLab est nécessaire pour générer le PDF.")
    aujourd_hui = datetime.now().strftime("%Y-%m-%d")
    with db() as c:
        factures = c.execute(
            "SELECT f.*, COALESCE((SELECT SUM(p.montant) FROM paiements p WHERE p.facture_id=f.id AND p.annule=0),0) AS paye "
            "FROM factures f ORDER BY substr(f.date_facture,7,4)||substr(f.date_facture,4,2)||substr(f.date_facture,1,2), f.id").fetchall()
        encaissements = c.execute(
            "SELECT p.id,p.date_iso,p.montant,p.mode,p.reference,f.id AS fid,f.client,f.immatriculation,f.date_facture,f.total "
            "FROM paiements p JOIN factures f ON f.id=p.facture_id WHERE p.annule=0 AND p.date_iso>=? ORDER BY p.date_iso,p.id",
            (aujourd_hui,)).fetchall()
    ouverts=[f for f in factures if float(f["total"] or 0)-float(f["paye"] or 0)>0.5]
    total_factures=sum(float(f["total"] or 0) for f in ouverts)
    total_avances=sum(float(f["paye"] or 0) for f in ouverts)
    total_reste=sum(max(0,float(f["total"] or 0)-float(f["paye"] or 0)) for f in ouverts)
    total_encaisses=sum(float(p["montant"] or 0) for p in encaissements)
    chemin=os.path.join(DOSSIER_PDF,"Recap_Factures_En_Cours_{}.pdf".format(datetime.now().strftime("%Y%m%d_%H%M%S")))
    c=canvas.Canvas(chemin,pagesize=A4); c.setTitle("Récapitulatif des factures en cours")
    L,R=40,555
    def entete(y=800):
        c.setFont("Helvetica-Bold",14); c.drawString(L,y,param("garage_nom"))
        c.setFont("Helvetica",9); c.drawString(L,y-15,param("garage_adresse")); c.drawString(L,y-28,param("garage_contact"))
        c.setFont("Helvetica-Bold",13); c.drawString(L,y-58,"RÉCAPITULATIF DES FACTURES EN COURS")
        c.setFont("Helvetica",9); c.drawString(L,y-74,"Situation au {} | Avances encaissées depuis le {}".format(datetime.now().strftime("%d/%m/%Y"),datetime.now().strftime("%d/%m/%Y")))
        return y-100
    y=entete()
    c.setFont("Helvetica-Bold",9); c.drawString(L,y,"Factures ouvertes : {}".format(len(ouverts)))
    c.drawString(L+165,y,"Total facturé : {} Ar".format(prix_affiche(total_factures)))
    y-=16;c.drawString(L+165,y,"Avances déjà reçues : {} Ar".format(prix_affiche(total_avances)))
    y-=16;c.drawString(L+165,y,"RESTE À ENCAISSER : {} Ar".format(prix_affiche(total_reste)))
    y-=30;c.setFont("Helvetica-Bold",8)
    c.drawString(L,y,"N° FACTURE / CLIENT");c.drawString(275,y,"TOTAL");c.drawString(365,y,"AVANCES");c.drawRightString(R,y,"RESTE (Ar)")
    y-=7;c.line(L,y,R,y);y-=14
    c.setFont("Helvetica",8)
    for f in ouverts:
        if y<70:
            c.showPage();y=entete()
            c.setFont("Helvetica-Bold",8);c.drawString(L,y,"N° FACTURE / CLIENT");c.drawString(275,y,"TOTAL");c.drawString(365,y,"AVANCES");c.drawRightString(R,y,"RESTE (Ar)");y-=18;c.setFont("Helvetica",8)
        num=numero_doc("FAC",f["id"],f["date_facture"])
        c.drawString(L,y,(num+" - "+str(f["client"] or ""))[:38])
        c.drawRightString(335,y,prix_affiche(f["total"]))
        c.drawRightString(435,y,prix_affiche(f["paye"]))
        c.drawRightString(R,y,prix_affiche(max(0,float(f["total"] or 0)-float(f["paye"] or 0))))
        y-=14
    y-=10
    if y<95:c.showPage();y=entete()
    c.setFont("Helvetica-Bold",10);c.drawString(L,y,"AVANCES / PAIEMENTS ENCAISSÉS DEPUIS AUJOURD'HUI")
    y-=18;c.setFont("Helvetica-Bold",8);c.drawString(L,y,"Date");c.drawString(100,y,"Client / facture");c.drawString(330,y,"Mode");c.drawString(425,y,"Référence");c.drawRightString(R,y,"Montant")
    y-=8;c.line(L,y,R,y);y-=14;c.setFont("Helvetica",8)
    for p in encaissements:
        if y<55:
            c.showPage();y=entete();y-=15;c.setFont("Helvetica-Bold",8)
        c.drawString(L,y,fr_depuis_iso(p["date_iso"]))
        c.drawString(100,y,(str(p["client"] or "")+" / "+numero_doc("FAC",p["fid"],p["date_facture"]))[:42])
        c.drawString(330,y,str(p["mode"] or "")[:18])
        if p["reference"]:
            c.drawString(425,y,("Réf: "+str(p["reference"]))[:18])
        c.drawRightString(R,y,prix_affiche(p["montant"]));y-=13
    if not encaissements:
        c.drawString(L,y,"Aucun paiement enregistré depuis aujourd'hui.");y-=14
    c.setFont("Helvetica-Bold",9);c.drawString(L,max(35,y-5),"Total encaissé depuis aujourd'hui : {} Ar".format(prix_affiche(total_encaisses)))
    c.save()
    return chemin


# ============================================================
# COMPTABILITÉ : paiements, journal, bilan fiscal
# ============================================================

# Seuils utilisés pour les ESTIMATIONS. Ils changent avec les lois de finances :
# à faire confirmer par votre centre des impôts ou votre comptable.
SEUIL_RECAP = 100_000_000   # entreprise individuelle : récapitulatif recettes/dépenses
SEUIL_IS = 200_000_000      # impôt synthétique en dessous de ce chiffre d'affaires
SEUIL_TVA = 400_000_000     # TVA obligatoire à partir de (optionnelle entre 200 et 400 M)

MODES = ["Espèces", "Banque / Virement bancaire", "Mobile Money - MVola", "Mobile Money - Orange Money", "Mobile Money - Airtel Money", "Mobile Money - autre", "Chèque", "Autre"]
CAT_SALAIRES = "Salaires et charges sociales"
CAT_IMPOTS = "Impôts et taxes"
CATEGORIES_DEPENSES = [
    "Achats de pièces et fournitures", "Sous-traitance", CAT_SALAIRES, "Loyer",
    "Eau, électricité, téléphone, internet", "Carburant et déplacements",
    "Outillage et petit matériel", "Investissement (gros équipement)", "Assurances",
    "Frais bancaires et Mobile Money", CAT_IMPOTS, "Autres dépenses"]
CATEGORIES_RECETTES = ["Vente comptoir (sans facture)", "Autres recettes"]
INVENTAIRE_CHAMPS = [
    ("stock", "Stock de pièces (valeur d'achat)"),
    ("materiel", "Matériel et outillage (valeur actuelle)"),
    ("tresorerie", "Trésorerie au 31/12 (caisse + banque + Mobile Money)"),
    ("dettes_fournisseurs", "Dettes envers les fournisseurs"),
    ("emprunts", "Emprunts en cours"),
    ("dettes_fiscales", "Dettes fiscales et sociales (impôts, CNaPS, IRSA)")]


def annees_choix():
    an = datetime.now().year
    return [str(a) for a in range(an, an - 6, -1)]


# ---- Paiements des factures (encaissements partiels possibles) -----------

def _maj_paye(c, fid):
    r = c.execute("SELECT f.total, COALESCE((SELECT SUM(montant) FROM paiements p "
                  "WHERE p.facture_id=f.id AND p.annule=0),0) AS paye FROM factures f WHERE f.id=?",
                  (fid,)).fetchone()
    if not r:
        raise ValueError("Facture introuvable.")
    c.execute("UPDATE factures SET paye=? WHERE id=?", (1 if r["paye"] >= r["total"] - 0.5 else 0, fid))
    return r["total"], r["paye"]


def infos_paiement(fid):
    with db() as c:
        total, paye = _maj_paye(c, fid)
        hist = c.execute("SELECT date_iso, montant, mode, reference FROM paiements WHERE facture_id=? "
                         "AND annule=0 ORDER BY id", (fid,)).fetchall()
    return total, paye, hist


def enregistrer_paiement(fid, montant, mode, date_fr="", reference=""): 
    montant = prix_nombre(montant)
    if montant <= 0:
        raise ValueError("Le montant doit être supérieur à 0.")
    if mode not in MODES:
        raise ValueError("Choisissez un mode de paiement valide.")
    date_iso = iso_depuis_fr(date_fr, strict=True) if str(date_fr).strip() else datetime.now().strftime("%Y-%m-%d")
    with db() as c:
        total, paye = _maj_paye(c, fid)
        reste = total - paye
        if montant > reste + 0.5:
            raise ValueError(f"Le montant dépasse le reste à payer ({prix_affiche(reste)}).")
        paiement_id = c.execute("INSERT INTO paiements (facture_id, date_iso, montant, mode, reference) VALUES (?,?,?,?,?)",
                                (fid, date_iso, montant, mode, reference)).lastrowid
        _maj_paye(c, fid)
    return paiement_id


def annuler_dernier_paiement(fid):
    with db() as c:
        r = c.execute("SELECT id FROM paiements WHERE facture_id=? AND annule=0 ORDER BY id DESC LIMIT 1",
                      (fid,)).fetchone()
        if not r:
            raise ValueError("Aucun paiement à annuler.")
        c.execute("UPDATE paiements SET annule=1 WHERE id=?", (r["id"],))
        _maj_paye(c, fid)


# ---- Écritures manuelles (dépenses, recettes sans facture) ---------------

def enregistrer_ecriture(sens, date_fr, categorie, libelle, tiers, montant, mode, piece):
    montant = prix_nombre(montant)
    if sens not in ("R", "D"):
        raise ValueError("Le type d'écriture doit être une recette ou une dépense.")
    if mode not in MODES:
        raise ValueError("Choisissez un mode de paiement valide.")
    if montant <= 0:
        raise ValueError("Le montant doit être supérieur à 0.")
    if not str(libelle).strip():
        raise ValueError("Le libellé est obligatoire.")
    date_iso = iso_depuis_fr(date_fr, strict=True)
    with db() as c:
        c.execute("INSERT INTO ecritures (date_iso, sens, categorie, libelle, tiers, montant, mode, piece, cree_le) "
                  "VALUES (?,?,?,?,?,?,?,?,?)",
                  (date_iso, sens, categorie, str(libelle).strip(), str(tiers).strip(), montant, mode,
                   str(piece).strip(), datetime.now().isoformat(timespec="seconds")))


def annuler_derniere_ecriture():
    """Un journal ne s'efface pas : l'écriture reste visible, marquée ANNULÉE, hors des totaux."""
    with db() as c:
        r = c.execute("SELECT id FROM ecritures WHERE annulee=0 ORDER BY id DESC LIMIT 1").fetchone()
        if not r:
            raise ValueError("Aucune écriture à annuler.")
        c.execute("UPDATE ecritures SET annulee=1 WHERE id=?", (r["id"],))


# ---- Journal et bilan ----------------------------------------------------

def lignes_journal(annee):
    debut, fin = f"{annee}-01-01", f"{annee}-12-31"
    out = []
    with db() as c:
        for r in c.execute("SELECT p.id, p.date_iso, p.montant, p.mode, p.annule, f.id AS fid, f.client, "
                           "f.vehicule, f.date_facture FROM paiements p JOIN factures f ON f.id=p.facture_id "
                           "WHERE p.date_iso BETWEEN ? AND ?", (debut, fin)):
            out.append({"date": r["date_iso"], "sens": "R", "src": "P", "ordre": r["id"],
                        "cat": "Encaissement facture", "lib": f"{r['client']} - {r['vehicule']}",
                        "tiers": r["client"], "piece": numero_doc("FAC", r["fid"], r["date_facture"]),
                        "montant": r["montant"], "mode": r["mode"], "annule": bool(r["annule"])})
        for r in c.execute("SELECT * FROM ecritures WHERE date_iso BETWEEN ? AND ?", (debut, fin)):
            out.append({"date": r["date_iso"], "sens": r["sens"], "src": "E", "ordre": r["id"],
                        "cat": r["categorie"], "lib": r["libelle"], "tiers": r["tiers"],
                        "piece": r["piece"], "montant": r["montant"], "mode": r["mode"],
                        "annule": bool(r["annulee"])})
    out.sort(key=lambda x: (x["date"], x["src"], x["ordre"]))
    for i, l in enumerate(out, 1):
        l["n"] = i
    return out


def regime_probable(ca):
    if ca < SEUIL_RECAP:
        return ("Impôt synthétique. Pour une entreprise individuelle, un récapitulatif des recettes "
                "et dépenses est en principe suffisant.")
    if ca < SEUIL_IS:
        return "Impôt synthétique. États financiers selon le Système Minimal de Trésorerie, à établir avec un comptable."
    if ca < SEUIL_TVA:
        return ("Régime du réel (impôt sur le revenu sur le bénéfice). TVA optionnelle entre 200 et 400 millions "
                "d'Ar. États financiers complets requis.")
    return "Régime du réel avec TVA obligatoire. États financiers complets requis."


def bilan_annee(annee):
    fin = f"{annee}-12-31"
    lignes = [l for l in lignes_journal(annee) if not l["annule"]]
    rec_fact = sum(l["montant"] for l in lignes if l["sens"] == "R" and l["src"] == "P")
    rec_autres = sum(l["montant"] for l in lignes if l["sens"] == "R" and l["src"] == "E")
    recettes = rec_fact + rec_autres
    dep_cat, achats_factures, salaires = {}, 0.0, 0.0
    for l in lignes:
        if l["sens"] != "D":
            continue
        dep_cat[l["cat"]] = dep_cat.get(l["cat"], 0) + l["montant"]
        if l["cat"] == CAT_SALAIRES:
            salaires += l["montant"]
        elif l["cat"] != CAT_IMPOTS and l["piece"]:  # achats « dûment facturés »
            achats_factures += l["montant"]
    depenses = sum(dep_cat.values())
    with db() as c:
        facture = sum(f["total"] for f in c.execute(
            "SELECT total FROM factures WHERE date_facture LIKE ?", (f"%/{annee}",)))
        creances = 0.0
        for f in c.execute("SELECT id, total, date_facture FROM factures"):
            if iso_depuis_fr(f["date_facture"]) <= fin:
                paye = c.execute("SELECT COALESCE(SUM(montant),0) FROM paiements WHERE facture_id=? "
                                 "AND annule=0 AND date_iso<=?", (f["id"], fin)).fetchone()[0]
                creances += max(f["total"] - paye, 0)
        inv = {r["cle"]: r["valeur"] for r in c.execute(
            "SELECT cle, valeur FROM inventaire WHERE annee=?", (annee,))}

    ca = recettes
    taux, red = prix_nombre(param("is_taux")), prix_nombre(param("is_reduction"))
    plancher, mini = prix_nombre(param("is_plancher")), prix_nombre(param("is_minimum"))
    is_brut = ca * taux / 100
    reduction = (achats_factures + salaires) * red / 100
    is_plancher = ca * plancher / 100
    is_net = max(is_brut - reduction, is_plancher, mini)
    actif = creances + inv.get("stock", 0) + inv.get("materiel", 0) + inv.get("tresorerie", 0)
    dettes = inv.get("dettes_fournisseurs", 0) + inv.get("emprunts", 0) + inv.get("dettes_fiscales", 0)
    return {"annee": annee, "rec_fact": rec_fact, "rec_autres": rec_autres, "recettes": recettes,
            "dep_cat": dep_cat, "depenses": depenses, "resultat": recettes - depenses,
            "facture": facture, "creances": creances, "ca": ca, "regime": regime_probable(ca),
            "achats_factures": achats_factures, "salaires": salaires, "taux": taux, "red": red,
            "plancher": plancher, "is_brut": is_brut, "reduction": reduction,
            "is_plancher": is_plancher, "is_net": is_net, "ir": max(recettes - depenses, 0) * 0.20,
            "inv": inv, "inv_saisi": bool(inv), "actif": actif, "dettes": dettes,
            "capitaux": actif - dettes}


def synthese(b):
    """Liste de (type, gauche, droite) : T=titre, L=ligne, B=ligne en gras, N=note."""
    S = []

    def T(t): S.append(("T", t, ""))
    def L(g, d="", gras=False): S.append(("B" if gras else "L", g, d))
    def N(t): S.append(("N", t, ""))

    T("1. RECETTES ENCAISSÉES")
    L("Encaissements de factures", prix_affiche(b["rec_fact"]))
    L("Autres recettes (comptoir...)", prix_affiche(b["rec_autres"]))
    L("TOTAL DES RECETTES", prix_affiche(b["recettes"]), True)
    T("2. DÉPENSES")
    for cat, m in sorted(b["dep_cat"].items(), key=lambda kv: -kv[1]):
        L(cat, prix_affiche(m))
    L("TOTAL DES DÉPENSES", prix_affiche(b["depenses"]), True)
    T("3. RÉSULTAT DE L'EXERCICE")
    L("Excédent (déficit) de trésorerie", prix_affiche(b["resultat"]), True)
    L("Facturé sur l'exercice", prix_affiche(b["facture"]))
    L("Créances clients au 31/12 (non encaissées)", prix_affiche(b["creances"]))
    T("4. SITUATION FISCALE (ESTIMATION INDICATIVE)")
    N("Régime probable : " + b["regime"])
    L("Base de l'impôt (encaissements)", prix_affiche(b["ca"]))
    if b["ca"] < SEUIL_IS:
        L(f"Impôt synthétique {b['taux']:g} %", prix_affiche(b["is_brut"]))
        L(f"Réduction {b['red']:g} % (achats facturés {prix_affiche(b['achats_factures'])}, "
          f"salaires {prix_affiche(b['salaires'])})", "-" + prix_affiche(b["reduction"]))
        L(f"Plancher {b['plancher']:g} % du chiffre d'affaires", prix_affiche(b["is_plancher"]))
        L("IMPÔT SYNTHÉTIQUE ESTIMÉ", prix_affiche(b["is_net"]), True)
        N(f"À déclarer et payer avant le 31 mars {b['annee'] + 1}.")
    else:
        L("Impôt sur le revenu indicatif (20 % du résultat)", prix_affiche(b["ir"]), True)
        N("Minimum de perception, amortissements, stocks et TVA : à calculer avec votre comptable.")
    T("5. SITUATION PATRIMONIALE SIMPLIFIÉE AU 31/12")
    if b["inv_saisi"]:
        L("Créances clients", prix_affiche(b["creances"]))
        for cle, lib in INVENTAIRE_CHAMPS[:3]:
            L(lib.split(" (")[0], prix_affiche(b["inv"].get(cle, 0)))
        L("TOTAL ACTIF", prix_affiche(b["actif"]), True)
        for cle, lib in INVENTAIRE_CHAMPS[3:]:
            L(lib.split(" (")[0], prix_affiche(b["inv"].get(cle, 0)))
        L("TOTAL DETTES", prix_affiche(b["dettes"]), True)
        L("CAPITAUX DE L'EXPLOITANT (actif - dettes)", prix_affiche(b["capitaux"]), True)
    else:
        N("Inventaire de fin d'année non saisi (bouton « Inventaire »).")
    N("Document de travail : il ne remplace pas les états financiers établis ou validés par un comptable agréé.")
    return S


def texte_synthese(S):
    out = []
    for t, g, d in S:
        if t == "T":
            out += ["", g]
        elif t in ("L", "B"):
            out.append(f"  {g} : {d}")
        else:
            out.append(f"  {g}")
    return "\n".join(out).strip()


def couper(txt, police, taille, largeur):
    t = str(txt)
    while t and stringWidth(t, police, taille) > largeur:
        t = t[:-1]
    return t


def generer_pdf_bilan(annee):
    if not HAS_REPORTLAB:
        return None
    b = bilan_annee(annee)
    lignes = lignes_journal(annee)
    chemin = os.path.join(DOSSIER_PDF, f"Recapitulatif_{annee}.pdf")
    c = canvas.Canvas(chemin, pagesize=A4)
    L, R = 40, 555
    etat = {"y": 700, "page": 1, "entete": None}

    def pied():
        c.setFont("Helvetica", 8)
        c.drawCentredString(297, 25, f"{param('garage_nom')} - Récapitulatif {annee} - Page {etat['page']}")

    def saut(h=14):
        if etat["y"] - h < 50:
            pied()
            c.showPage()
            etat["page"] += 1
            etat["y"] = 800
            if etat["entete"]:
                etat["entete"]()

    def ligne(gauche, droite="", gras=False):
        saut()
        c.setFont("Helvetica-Bold" if gras else "Helvetica", 9)
        c.drawString(L + 10, etat["y"], couper(gauche, c._fontname, 9, 370))
        if droite:
            c.drawRightString(R, etat["y"], droite)
        etat["y"] -= 13

    def section(t):
        saut(40)
        etat["y"] -= 8
        c.setFont("Helvetica-Bold", 11)
        c.drawString(L, etat["y"], t)
        c.line(L, etat["y"] - 3, R, etat["y"] - 3)
        etat["y"] -= 18

    def note(t):
        c.setFont("Helvetica-Oblique", 8)
        for morceau in simpleSplit(t, "Helvetica-Oblique", 8, 500):
            saut(11)
            c.setFont("Helvetica-Oblique", 8)
            c.drawString(L + 10, etat["y"], morceau)
            etat["y"] -= 11

    c.setFont("Helvetica-Bold", 14)
    c.drawString(L, 800, param("garage_nom"))
    c.setFont("Helvetica", 9)
    for i, cle in enumerate(("garage_adresse", "garage_nif", "garage_contact")):
        c.drawString(L, 786 - 13 * i, param(cle))
    c.setFont("Helvetica-Bold", 13)
    c.drawString(L, 725, f"RÉCAPITULATIF DES RECETTES ET DÉPENSES - EXERCICE {annee}")

    for t, g, d in synthese(b):
        if t == "T":
            section(g)
        elif t == "N":
            note(g)
        else:
            ligne(g, d, t == "B")

    def entete_journal():
        c.setFont("Helvetica-Bold", 8)
        y = etat["y"]
        c.drawString(L, y, "N°")
        c.drawString(L + 22, y, "Date")
        c.drawString(L + 75, y, "Catégorie - libellé")
        c.drawString(L + 330, y, "Pièce")
        c.drawRightString(475, y, "Recette")
        c.drawRightString(R, y, "Dépense")
        c.line(L, y - 3, R, y - 3)
        etat["y"] -= 14

    section("6. JOURNAL DÉTAILLÉ")
    entete_journal()
    etat["entete"] = entete_journal
    for l in lignes:
        saut(12)
        y = etat["y"]
        c.setFont("Helvetica", 7.5)
        c.drawString(L, y, str(l["n"]))
        c.drawString(L + 22, y, fr_depuis_iso(l["date"]))
        txt = f"{l['cat']} - {l['lib']}" + ("  [ANNULÉE]" if l["annule"] else "")
        c.drawString(L + 75, y, couper(txt, "Helvetica", 7.5, 250))
        c.drawString(L + 330, y, couper(l["piece"], "Helvetica", 7.5, 55))
        if not l["annule"]:
            c.drawRightString(475 if l["sens"] == "R" else R, y, prix_affiche(l["montant"]))
        etat["y"] -= 11
    etat["entete"] = None
    pied()
    c.save()
    return chemin


def exporter_csv(annee):
    chemin = os.path.join(DOSSIER_PDF, f"Journal_{annee}.csv")
    def cellule_csv(valeur):
        # Empêche Excel/Calc d'interpréter un texte saisi comme une formule.
        texte = str(valeur if valeur is not None else "")
        if texte.lstrip().startswith(("=", "+", "-", "@")):
            return "'" + texte
        return texte
    with open(chemin, "w", newline="", encoding="utf-8-sig") as f:  # s'ouvre directement dans Excel
        w = csv.writer(f, delimiter=";")
        w.writerow(["N°", "Date", "Catégorie", "Libellé", "Tiers", "Pièce", "Mode",
                    "Recette (Ar)", "Dépense (Ar)", "Statut"])
        for l in lignes_journal(annee):
            m = nombre_txt(l["montant"])
            w.writerow([l["n"], fr_depuis_iso(l["date"]), cellule_csv(l["cat"]), cellule_csv(l["lib"]),
                        cellule_csv(l["tiers"]), cellule_csv(l["piece"]), cellule_csv(l["mode"]),
                        m if l["sens"] == "R" else "", m if l["sens"] == "D" else "",
                        "ANNULÉE" if l["annule"] else "Valide"])
    return chemin


def exporter_bilan(annee):
    return generer_pdf_bilan(annee), exporter_csv(annee)


@securise
def exporter_dialogue(annee):
    pdf, fichier_csv = exporter_bilan(annee)
    popup_actions("Export prêt", f"Récapitulatif {annee} (PDF) et journal (CSV) créés.", [
        ("Ouvrir le PDF", BLEU, (lambda: ouvrir_ou_partager(pdf)) if pdf else
         (lambda: afficher_popup("PDF indisponible", "Installez reportlab."))),
        ("Partager le journal (CSV)", ORANGE, lambda: ouvrir_ou_partager(fichier_csv)),
        ("Fermer", GRIS, None)])


@securise
def envoyer_au_comptable(annee):
    dest = param("email_comptable").strip()
    if not dest:
        afficher_popup("E-mail du comptable", "Renseignez-le dans Paramètres.")
        return
    pdf, fichier_csv = exporter_bilan(annee)
    attente = afficher_popup("Envoi en cours", f"Envoi à {dest}...")

    def fin(ok, info):
        attente.dismiss()
        afficher_popup("Envoyé" if ok else "Échec de l'envoi", f"Envoyé à {dest}." if ok else info)

    envoyer_email(dest, f"Journal et récapitulatif {annee} - {param('garage_nom')}",
                  f"Bonjour,\n\nCi-joint le récapitulatif des recettes et dépenses {annee} et le journal "
                  f"détaillé (CSV).\n\nCordialement,\n{param('garage_nom')}\n{param('garage_contact')}",
                  [p for p in (pdf, fichier_csv) if p], fin)


# ============================================================
# E-MAIL ET PARTAGE
# ============================================================

def envoyer_email(destinataire, sujet, corps, piece_jointe, callback):
    """Envoi SMTP en arrière-plan, avec diagnostic et essai du port Gmail alternatif."""
    hote = (param("smtp_hote") or "smtp.gmail.com").strip()
    try:
        port = int(prix_nombre(param("smtp_port")) or 465)
    except (TypeError, ValueError):
        port = 465
    user = (param("smtp_user") or "").strip()
    mdp = str(param("smtp_mdp") or "").strip()
    nom = param("garage_nom") or "Clinique Auto Mada"
    if not (hote and user and mdp):
        callback(False, "Configurez le serveur SMTP, l'adresse Gmail complète et le mot de passe d'application dans Paramètres.")
        return
    if port not in (465, 587):
        callback(False, "Pour Gmail, choisissez le port 465 (SSL/TLS) ou 587 (STARTTLS).")
        return

    def tache():
        srv = None
        try:
            msg = EmailMessage()
            msg["From"] = f"{nom} <{user}>"
            msg["To"] = destinataire
            msg["Subject"] = sujet
            msg.set_content(corps)
            pieces = [piece_jointe] if isinstance(piece_jointe, str) else (piece_jointe or [])
            for pj in pieces:
                typ = (mimetypes.guess_type(pj)[0] or "application/octet-stream").split("/")
                with open(pj, "rb") as f:
                    msg.add_attachment(f.read(), maintype=typ[0], subtype=typ[1],
                                       filename=os.path.basename(pj))

            contexte = ssl.create_default_context()
            ports = [port, 587 if port == 465 else 465]
            dernier_probleme = None
            # On ne bascule vers l'autre port que si la connexion/TLS échoue,
            # avant l'authentification et l'envoi du message.
            for essai_port in ports:
                srv = None
                try:
                    if essai_port == 465:
                        srv = smtplib.SMTP_SSL(hote, essai_port, timeout=25, context=contexte)
                        srv.ehlo()
                    else:
                        srv = smtplib.SMTP(hote, essai_port, timeout=25)
                        srv.ehlo()
                        srv.starttls(context=contexte)
                        srv.ehlo()
                    break
                except (OSError, ssl.SSLError, smtplib.SMTPException) as e:
                    dernier_probleme = e
                    if srv is not None:
                        try:
                            srv.close()
                        except Exception:
                            pass
                    srv = None
            if srv is None:
                raise RuntimeError(
                    "Connexion sécurisée à Gmail impossible sur les ports 465 et 587. "
                    "Les ports répondent, mais la négociation SSL/TLS échoue. "
                    "Vérifiez la date/heure de Windows, l'antivirus et le pare-feu. "
                    "Détail technique : {}".format(dernier_probleme)
                )

            # Les erreurs d'identification sont séparées des erreurs de connexion.
            try:
                srv.login(user, mdp)
            except smtplib.SMTPAuthenticationError as e:
                raise RuntimeError(
                    "Gmail refuse l'identification. Utilisez l'adresse Gmail complète "
                    "et un mot de passe d'application Google (16 caractères), pas le "
                    "mot de passe habituel. Détail : {}".format(e)
                )
            srv.send_message(msg)
            srv.quit()
            srv = None
            ok, info = True, ""
        except socket.gaierror as e:
            ok, info = False, "Nom du serveur introuvable (DNS). Vérifiez smtp.gmail.com et Internet. Détail : {}".format(e)
        except ssl.SSLError as e:
            ok, info = False, "Échec SSL/TLS. Vérifiez la date/heure de Windows, les certificats et l'antivirus. Détail : {}".format(e)
        except smtplib.SMTPServerDisconnected as e:
            ok, info = False, "Gmail a fermé la connexion avant la fin de l'envoi. Vérifiez SSL/TLS, l'antivirus/pare-feu et le mot de passe d'application. Détail : {}".format(e)
        except Exception as e:
            ok, info = False, str(e)
        finally:
            if srv is not None:
                try:
                    srv.quit()
                except Exception:
                    try:
                        srv.close()
                    except Exception:
                        pass
        Clock.schedule_once(lambda dt: callback(ok, info))

    threading.Thread(target=tache, daemon=True).start()


def _message_client(type_doc, doc, numero):
    corrige = type_doc == "Devis" and doc["version"] > 1
    intro = "Voici la version corrigée de votre devis" if corrige else f"Veuillez trouver votre {type_doc.lower()}"
    return (f"Bonjour {doc['client']},\n\n{intro} N° {numero} pour le véhicule "
            f"{doc['vehicule']} ({doc['immatriculation']}).\nMontant total : {prix_affiche(doc['total'])}.\n\n"
            f"Cordialement,\n{param('garage_nom')}\n{param('garage_contact')}")


@securise
def envoyer_document(type_doc, doc_id):
    chemin, doc = regenerer_pdf(type_doc, doc_id)
    if not chemin:
        afficher_popup("PDF indisponible", "Installez la bibliothèque reportlab.")
        return
    if not doc["email"]:
        afficher_popup("E-mail manquant", "Ce client n'a pas d'adresse e-mail.\n"
                                          "Modifiez le devis pour l'ajouter.")
        return
    numero = numero_doc("DEV" if type_doc == "Devis" else "FAC", doc_id, doc["date"])
    corrige = type_doc == "Devis" and doc["version"] > 1
    sujet = f"{type_doc}{' corrigé' if corrige else ''} N° {numero} - {doc['vehicule']} ({doc['immatriculation']})"
    attente = afficher_popup("Envoi en cours", f"Envoi à {doc['email']}...")

    def fin(ok, info):
        attente.dismiss()
        if ok:
            afficher_popup("Envoyé", f"{type_doc} {numero} envoyé à\n{doc['email']}")
        else:
            afficher_popup("Échec de l'envoi", info)

    envoyer_email(doc["email"], sujet, _message_client(type_doc, doc, numero), chemin, fin)


@securise
def partager_whatsapp(type_doc, doc_id):
    """Génère le PDF puis utilise le flux WhatsApp commun avec confirmation."""
    chemin, doc = regenerer_pdf(type_doc, doc_id)
    if not chemin or not os.path.isfile(chemin):
        afficher_popup("PDF indisponible", "Le PDF n'a pas pu être créé. Vérifiez ReportLab.")
        return
    numero = numero_doc("DEV" if type_doc == "Devis" else "FAC", doc_id, doc["date"])
    message = _message_client(type_doc, doc, numero)
    partager_pdf_whatsapp(doc.get("tel", ""), message, chemin, f"{type_doc} {numero}")


@securise
def voir_pdf(type_doc, doc_id):
    chemin, _ = regenerer_pdf(type_doc, doc_id)
    if chemin:
        ouvrir_ou_partager(chemin)
    else:
        afficher_popup("PDF indisponible", "Installez la bibliothèque reportlab.")


# ============================================================
# ÉCRAN DEVIS (création + modification)
# ============================================================

class LigneDevis(BoxLayout):

    def __init__(self, parent_devis, valeurs=None, **kwargs):
        super().__init__(orientation="horizontal", spacing=dp(5), size_hint_y=None,
                         height=dp(46), **kwargs)
        v = valeurs or {}
        self.parent_devis = parent_devis
        self.type_ligne = Spinner(text=v.get("type", "Pièce"), values=("Pièce", "M.O."), size_hint_x=0.18)
        self.designation = TextInput(text=v.get("designation", ""), hint_text="Désignation",
                                     multiline=False, font_size=sp(13), size_hint_x=0.36)
        self.quantite = TextInput(text=nombre_txt(v.get("quantite", 1)), multiline=False,
                                  input_filter="float", font_size=sp(13), size_hint_x=0.10)
        self.prix = TextInput(text=nombre_txt(v.get("prix", 0)), multiline=False,
                              input_filter="float", font_size=sp(13), size_hint_x=0.18)
        self.total = Label(text="0 Ar", font_size=sp(12), bold=True, color=BLEU_FONCE, size_hint_x=0.18)
        btn = Button(text="X", font_size=sp(13), bold=True, size_hint_x=None, width=dp(36),
                     background_normal="", background_color=ROUGE)

        for w in (self.type_ligne, self.designation, self.quantite, self.prix, self.total, btn):
            self.add_widget(w)

        self.quantite.bind(text=self.changement)
        self.prix.bind(text=self.changement)
        self.type_ligne.bind(text=self.changement)
        self.designation.bind(focus=self.sur_focus)
        btn.bind(on_release=lambda x: self.parent_devis.supprimer_ligne(self))
        self.changement()

    def changement(self, *args):
        self.total.text = prix_affiche(prix_nombre(self.quantite.text) * prix_nombre(self.prix.text))
        self.parent_devis.calculer_totaux()

    def sur_focus(self, inst, focus):
        """Innovation : pré-remplit le prix avec le dernier prix utilisé pour cette pièce."""
        if not focus and inst.text.strip() and prix_nombre(self.prix.text) == 0:
            try:
                p = dernier_prix(inst.text.strip(), self.parent_devis.champs["marque"].text.strip())
            except Exception:
                p = 0
            if p:
                self.prix.text = nombre_txt(p)


class DevisScreen(Screen):

    CHAMPS = [("client", "Client (ex: MME TSIFERANA)", "text"),
              ("telephone", "Téléphone", "tel"),
              ("email", "E-mail du client", "mail"),
              ("marque", "Marque / Modèle (ex: Terracan)", "text"),
              ("immat", "Immatriculation (ex: 1921TBH)", "text"),
              ("moteur", "Moteur (ex: D4CB)", "text"),
              ("vin", "N° de série / VIN (châssis)", "text"),
              ("km", "Kilométrage (ex: 200250)", "number")]

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.lignes = []
        self.devis_id = None
        self.taux = 0.0

        principal = BoxLayout(orientation="vertical", padding=dp(12), spacing=dp(8))
        self.titre_lbl = titre("NOUVEAU DEVIS")
        principal.add_widget(self.titre_lbl)

        infos = GridLayout(cols=2, spacing=dp(6), size_hint_y=None, height=dp(200))
        self.champs = {}
        for cle, hint, typ in self.CHAMPS:
            ti = TextInput(hint_text=hint, multiline=False, font_size=sp(13), input_type=typ)
            self.champs[cle] = ti
            infos.add_widget(ti)
        principal.add_widget(infos)
        self.date_lbl = etiquette("", 13, BLEU_FONCE, True, 22)
        principal.add_widget(self.date_lbl)
        self.info_lbl = etiquette("", 11, GRIS_TEXTE, False, 24)
        principal.add_widget(self.info_lbl)
        self._auto_valeurs = {}
        for cle in ("client", "telephone", "email", "marque", "immat"):
            self.champs[cle].bind(focus=self._callback_focus(cle))

        barre = BoxLayout(size_hint_y=None, height=dp(32), spacing=dp(5))
        for t, w in [("TYPE", 0.18), ("DÉSIGNATION", 0.36), ("QTÉ", 0.10), ("P.U.", 0.18), ("TOTAL", 0.18)]:
            barre.add_widget(Label(text=t, bold=True, font_size=sp(11), color=BLEU_FONCE, size_hint_x=w))
        barre.add_widget(Label(text="", size_hint_x=None, width=dp(36)))
        principal.add_widget(barre)

        scroll = ScrollView(size_hint_y=1)
        self.zone_lignes = GridLayout(cols=1, spacing=dp(4), size_hint_y=None)
        self.zone_lignes.bind(minimum_height=self.zone_lignes.setter("height"))
        scroll.add_widget(self.zone_lignes)
        principal.add_widget(scroll)

        barre_lignes = BoxLayout(size_hint_y=None, height=dp(42), spacing=dp(6))
        btn_ajout = bouton("+ AJOUTER UNE LIGNE", BLEU, 40)
        btn_ajout.bind(on_release=lambda x: self.ajouter_ligne())
        btn_ia = bouton("ASSISTANT DE DEVIS (IA)", ORANGE, 40)
        btn_ia.bind(on_release=lambda x: self.ouvrir_assistant_devis())
        barre_lignes.add_widget(btn_ajout)
        barre_lignes.add_widget(btn_ia)
        principal.add_widget(barre_lignes)

        barre_controle = BoxLayout(size_hint_y=None, height=dp(42), spacing=dp(6))
        b_controle = bouton("CONTRÔLER PRIX / QTÉ", VERT, 40)
        b_controle.bind(on_release=lambda x: self.ouvrir_controle_devis())
        b_infos = bouton("FICHE / HISTORIQUE CLIENT", BLEU_FONCE, 40)
        b_infos.bind(on_release=lambda x: self.ouvrir_infos_client())
        barre_controle.add_widget(b_controle)
        barre_controle.add_widget(b_infos)
        principal.add_widget(barre_controle)

        self.total_general = Label(text="", font_size=sp(16), bold=True, color=VERT,
                                   size_hint_y=None, height=dp(30))
        principal.add_widget(self.total_general)

        actions = BoxLayout(size_hint_y=None, height=dp(45), spacing=dp(6))
        b1 = bouton("ENREGISTRER", VERT, 45)
        b1.bind(on_release=lambda x: self.enregistrer())
        b2 = bouton("RETOUR", BLEU_FONCE, 45)
        b2.bind(on_release=lambda x: setattr(self.manager, "current", "accueil"))
        actions.add_widget(b1)
        actions.add_widget(b2)
        principal.add_widget(actions)

        self.add_widget(principal)
        self.reinitialiser()

    # -- gestion du formulaire ---------------------------------
    def reinitialiser(self):
        self.devis_id = None
        self.taux = prix_nombre(param("tva_taux"))
        for w in self.champs.values():
            w.text = ""
        self.zone_lignes.clear_widgets()
        self.lignes = []
        self.titre_lbl.text = "NOUVEAU DEVIS"
        self.date_lbl.text = "Date : " + datetime.now().strftime("%d/%m/%Y")
        self.info_lbl.text = ""
        self._auto_valeurs = {}
        self.ajouter_ligne()

    def charger(self, devis_id):
        """Ouvre un devis existant pour le corriger."""
        doc = charger_document("Devis", devis_id)
        self.reinitialiser()
        self.zone_lignes.clear_widgets()
        self.lignes = []
        self.devis_id = devis_id
        self.taux = doc["tva_taux"]
        valeurs = {"client": doc["client"], "telephone": doc["tel"], "email": doc["email"],
                   "marque": doc["vehicule"], "immat": doc["immatriculation"],
                   "moteur": doc["moteur"], "vin": doc["vin"], "km": doc["km"]}
        for k, v in valeurs.items():
            self.champs[k].text = str(v or "")
        self._totaux_suspendus = True        # un seul calcul à la fin (et non un par ligne)
        try:
            for l in doc["lignes"]:
                self.ajouter_ligne(l)
            if not self.lignes:
                self.ajouter_ligne()
        finally:
            self._totaux_suspendus = False
        self.titre_lbl.text = f"MODIFIER LE DEVIS {numero_doc('DEV', devis_id, doc['date'])}"
        self.date_lbl.text = f"Date : {doc['date']} (rév. {doc['version']})"
        self.calculer_totaux()

    def reutiliser(self, devis_id):
        """Reprend un ancien devis comme nouveau brouillon sans modifier l'original."""
        doc = charger_document("Devis", devis_id)
        self.reinitialiser()
        self.zone_lignes.clear_widgets()
        self.lignes = []
        # Important : garder devis_id à None pour créer un NOUVEAU devis à l'enregistrement.
        self.devis_id = None
        self.taux = doc["tva_taux"]
        valeurs = {"client": doc["client"], "telephone": doc["tel"], "email": doc["email"],
                   "marque": doc["vehicule"], "immat": doc["immatriculation"],
                   "moteur": doc["moteur"], "vin": doc["vin"], "km": doc["km"]}
        for k, v in valeurs.items():
            self.champs[k].text = str(v or "")
        self._totaux_suspendus = True        # un seul calcul à la fin (et non un par ligne)
        try:
            for l in doc["lignes"]:
                self.ajouter_ligne(l)
            if not self.lignes:
                self.ajouter_ligne()
        finally:
            self._totaux_suspendus = False
        self.titre_lbl.text = f"NOUVEAU DEVIS — REPRIS DE {numero_doc('DEV', devis_id, doc['date'])}"
        self.date_lbl.text = "Date : " + datetime.now().strftime("%d/%m/%Y")
        self.info_lbl.text = "Copie de travail : vérifiez le kilométrage, les quantités et les prix avant d'enregistrer."
        self.calculer_totaux()

    def preremplir(self, valeurs):
        """Nouveau devis avec client / véhicule déjà remplis (depuis une recherche)."""
        self.reinitialiser()
        for k, v in valeurs.items():
            if k in self.champs:
                self.champs[k].text = str(v or "")

    def ajouter_ligne(self, valeurs=None):
        ligne = LigneDevis(self, valeurs)
        self.lignes.append(ligne)
        self.zone_lignes.add_widget(ligne)
        self.calculer_totaux()

    def supprimer_ligne(self, ligne):
        if ligne in self.lignes:
            self.lignes.remove(ligne)
            self.zone_lignes.remove_widget(ligne)
            self.calculer_totaux()

    def ouvrir_assistant_devis(self):
        """Assistant local : propose des lignes, sans enregistrer le devis."""
        contenu = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(8))
        contenu.add_widget(etiquette(
            "Une ligne par élément, ou un forfait. Exemples :\n"
            "2 x filtre à huile\nM.O. : vidange moteur\nrévision totale",
            13, BLEU_FONCE, True, 62))
        saisie = TextInput(
            hint_text="Décris les pièces et travaux...", multiline=True,
            size_hint_y=0.38, font_size=sp(14))
        contenu.add_widget(saisie)
        apercu = Label(text="Les suggestions utiliseront uniquement les prix déjà enregistrés.",
                       size_hint_y=0.38, halign="left", valign="top", font_size=sp(17),
                       bold=True, color=(1, 1, 1, 1))
        apercu.bind(size=lambda inst, val: setattr(inst, "text_size", val))
        contenu.add_widget(apercu)
        actions = BoxLayout(size_hint_y=None, height=dp(44), spacing=dp(5))
        b_analyser = bouton("ANALYSER", BLEU, 42)
        b_ia = bouton("ANALYSER AVEC IA", BLEU, 42)
        b_extraire = bouton("EXTRAIRE FICHE", BLEU_FONCE, 42)
        b_ajouter = bouton("AJOUTER AU DEVIS", VERT, 42)
        b_fermer = bouton("FERMER", GRIS, 42)
        actions.add_widget(b_analyser)
        actions.add_widget(b_ia)
        actions.add_widget(b_extraire)
        actions.add_widget(b_ajouter)
        actions.add_widget(b_fermer)
        contenu.add_widget(actions)
        popup = Popup(title="Assistant de devis (hors ligne + IA)", content=contenu,
                      size_hint=(0.94, 0.88), auto_dismiss=False,
                      background_color=BLEU_FONCE, title_color=(1, 1, 1, 1))
        popup.suggestions = []

        def contexte():
            return (self.champs["marque"].text.strip(), self.champs["km"].text.strip(),
                    self.champs["moteur"].text.strip())

        def afficher(suggestions, prefixe=""):
            popup.suggestions = suggestions
            if not suggestions:
                apercu.text = ("Aucune ligne reconnue. Écris une pièce ou prestation par ligne "
                               "(ex : 2 x filtre à huile) ou un forfait (ex : révision totale).")
                return
            lignes_texte = []
            for i, l in enumerate(suggestions, 1):
                prix_txt = prix_affiche(l["prix"]) if l["prix"] > 0 else "À saisir"
                lignes_texte.append(
                    f"{i}. [{l['type']}] {l['quantite']:g} x {l['designation']}\n"
                    f"   P.U. : {prix_txt} — {l['source_prix']}"
                    + (f"\n   Note : {l['note']}" if l.get("note") else "")
                )
            apercu.text = prefixe + "\n\n".join(lignes_texte)

        def analyser(*_):
            try:
                prefixe = self._prefixe_infos(saisie.text)
                afficher(suggerer_lignes_devis_hors_ligne(saisie.text, *contexte()), prefixe)
            except Exception as exc:
                popup.suggestions = []
                apercu.text = "Analyse impossible : " + str(exc)

        def analyser_ia(*_):
            if not str(saisie.text).strip():
                apercu.text = "Saisis d'abord une demande."
                return
            if not ia_disponible():
                apercu.text = ("IA désactivée. Paramètres > « IA activée » = Oui "
                               "et saisis ta clé API. L'analyse hors ligne reste disponible.")
                return
            apercu.text = "L'IA analyse la demande..."
            popup.suggestions = []
            texte = saisie.text
            prefixe = self._prefixe_infos(texte)
            ctx = contexte()

            def tache():
                try:
                    res = suggerer_lignes_devis_ia(texte, *ctx)
                    Clock.schedule_once(lambda dt: afficher(res, prefixe + "Analyse IA (prix = historique)\n\n"))
                except Exception as exc:
                    # Repli automatique : l'assistant hors ligne prend le relais
                    msg = str(exc)
                    def repli(dt):
                        try:
                            afficher(suggerer_lignes_devis_hors_ligne(texte, *ctx),
                                     prefixe + f"IA indisponible ({msg})\nAnalyse hors ligne à la place :\n\n")
                        except Exception as exc2:
                            apercu.text = "Analyse impossible : " + str(exc2)
                    Clock.schedule_once(repli)

            threading.Thread(target=tache, daemon=True).start()

        def ajouter(*_):
            if not popup.suggestions:
                analyser()
            if not popup.suggestions:
                return
            for w in [x for x in self.lignes if not x.designation.text.strip()
                      and prix_nombre(x.prix.text) == 0]:
                self.supprimer_ligne(w)           # retire la ligne vide du départ
            for suggestion in popup.suggestions:
                self.ajouter_ligne({
                    "type": suggestion["type"],
                    "designation": suggestion["designation"],
                    "quantite": suggestion["quantite"],
                    "prix": suggestion["prix"]
                })
            popup.dismiss()
            afficher_popup(
                "Suggestions ajoutées",
                "Les lignes sont dans le formulaire, mais rien n'est encore enregistré. "
                "Vérifie les désignations, quantités et prix, puis enregistre le devis."
            )

        def extraire_fiche(*_):
            infos = extraire_infos_texte(saisie.text)
            correspondances = {"client":"client", "telephone":"telephone", "email":"email",
                               "marque":"marque", "immat":"immat", "km":"km",
                               "moteur":"moteur", "vin":"vin"}
            propositions_fiche = []
            for source, cible in correspondances.items():
                valeur = infos.get(source, "")
                if valeur and cible in self.champs and not self.champs[cible].text.strip():
                    propositions_fiche.append((cible, str(valeur)))
            if not propositions_fiche:
                afficher_popup("Extraction du texte", "Aucune information exploitable à ajouter aux champs vides. Vérifiez les libellés, la plaque et le kilométrage.")
                return
            apercu.text = "Informations détectées (aucun champ modifié pour l'instant) :\n" + "\n".join(
                f"• {cible} : {valeur}" for cible, valeur in propositions_fiche)
            def appliquer_extraction():
                faits = []
                for cible, valeur in propositions_fiche:
                    if not self.champs[cible].text.strip():
                        self.champs[cible].text = valeur
                        faits.append(cible)
                self.remplir_depuis_texte(saisie.text)   # complète aussi téléphone / e-mail d'un client connu
                if faits:
                    afficher_popup("Fiche préremplie", "Champs complétés : " + ", ".join(faits) + ". Vérifiez les informations avant d'enregistrer.")
            popup_actions("Confirmer le préremplissage", apercu.text + "\n\nSeuls les champs vides seront complétés.", [
                ("APPLIQUER", VERT, appliquer_extraction), ("ANNULER", GRIS, None)])

        b_analyser.bind(on_release=analyser)
        b_ia.bind(on_release=analyser_ia)
        b_extraire.bind(on_release=extraire_fiche)
        b_ajouter.bind(on_release=ajouter)
        b_fermer.bind(on_release=lambda *_: popup.dismiss())
        popup.open()

    _LIBELLES = {"client": "client", "telephone": "tél.", "email": "e-mail", "marque": "véhicule",
                 "immat": "plaque", "moteur": "moteur", "vin": "VIN", "km": "km"}

    def remplir_depuis_texte(self, texte):
        """Lit une phrase libre (client, véhicule, km...) et complète les champs VIDES."""
        remplis = []
        for k, v in extraire_infos_texte(texte).items():
            w = self.champs.get(k)
            if w is not None and v and not w.text.strip():
                w.text = str(v)
                self._auto_valeurs[k] = str(v)
                remplis.append(self._LIBELLES[k])
        nom = self.champs["client"].text.strip()
        if nom and not (self.champs["telephone"].text.strip() and self.champs["email"].text.strip()):
            r = chercher_fiche("client", nom)
            if r["statut"] == "exact":
                f = r["fiches"][0]
                for k in ("telephone", "email"):
                    if f.get(k) and not self.champs[k].text.strip():
                        self.champs[k].text = f[k]
                        self._auto_valeurs[k] = f[k]
                        remplis.append(self._LIBELLES[k])
        return remplis

    def _prefixe_infos(self, texte):
        """Simple indication : le préremplissage se fait avec EXTRAIRE FICHE, après confirmation."""
        try:
            libres = [self._LIBELLES[k] for k, v in extraire_infos_texte(texte).items()
                      if v and k in self.champs and not self.champs[k].text.strip()]
        except Exception:
            libres = []
        return ("Infos détectées pour le formulaire (" + ", ".join(libres)
                + ") : touchez EXTRAIRE FICHE pour les ajouter.\n\n") if libres else ""

    def _callback_focus(self, cle):
        def cb(inst, focus):
            if not focus:
                Clock.schedule_once(lambda dt: self.auto_remplir(cle), 0.15)
                if cle == "email" and proposer_correction_email:
                    def verifier_email(dt):
                        valeur = self.champs["email"].text.strip()
                        suggestion = proposer_correction_email(valeur)
                        if suggestion:
                            afficher_popup("Vérifier l’e-mail", "Adresse saisie : " + valeur + "\nSuggestion possible : " + suggestion + "\nAucune modification appliquée : corrige-la manuellement si elle est exacte.")
                    Clock.schedule_once(verifier_email, 0.2)
        return cb

    @securise
    def auto_remplir(self, cle):
        valeur = self.champs[cle].text.strip()
        if not valeur or self._auto_valeurs.get(cle) == valeur:
            return
        self._auto_valeurs[cle] = valeur
        fiche = None
        with db() as c:
            if cle == "immat":
                fiche = c.execute("SELECT c.nom AS client, c.telephone, c.email, v.marque, v.modele, v.immatriculation AS immat, v.moteur, v.vin, v.kilometrage AS km "
                                  "FROM vehicules v LEFT JOIN clients c ON c.id=v.client_id WHERE compact(v.immatriculation)=compact(?) ORDER BY v.id DESC LIMIT 1", (valeur,)).fetchone()
                if not fiche and cle_plaque:
                    vehs = c.execute("SELECT v.id, v.immatriculation FROM vehicules v ORDER BY v.id DESC LIMIT 500").fetchall()
                    cand, score = meilleure_correspondance(cle_plaque(valeur), [dict(id=x["id"], nom=cle_plaque(x["immatriculation"])) for x in vehs], 0.88)
                    if cand is not None:
                        fiche = c.execute("SELECT c.nom AS client, c.telephone, c.email, v.marque, v.modele, v.immatriculation AS immat, v.moteur, v.vin, v.kilometrage AS km FROM vehicules v LEFT JOIN clients c ON c.id=v.client_id WHERE v.id=?", (cand["id"],)).fetchone()
                        if fiche:
                            self.info_lbl.text = "Plaque proche trouvée (" + str(int(score*100)) + " %) : vérifie l'immatriculation avant enregistrement."
            elif cle == "client":
                cl = c.execute("SELECT * FROM clients WHERE norm(nom)=norm(?) OR norm(nom) LIKE ? ORDER BY id DESC LIMIT 1", (valeur, "%"+valeur+"%")).fetchone()
                # Repli flou prudent : seulement si la correspondance est nette; jamais de choix ambigu.
                if not cl and meilleure_correspondance:
                    candidats = [dict(id=r["id"], nom=r["nom"]) for r in c.execute("SELECT id, nom FROM clients ORDER BY id DESC LIMIT 500").fetchall()]
                    candidat, score = meilleure_correspondance(valeur, candidats, 0.84)
                    if candidat is not None:
                        cl = c.execute("SELECT * FROM clients WHERE id=?", (candidat["id"],)).fetchone()
                        self.info_lbl.text = "Correspondance probable du client (" + str(int(score*100)) + " %) : vérifie le nom avant d'enregistrer."
                if cl:
                    veh = c.execute("SELECT marque, modele, immatriculation AS immat, moteur, vin, kilometrage AS km FROM vehicules WHERE client_id=? ORDER BY id DESC LIMIT 1", (cl["id"],)).fetchone()
                    fiche = dict(client=cl["nom"], telephone=cl["telephone"], email=cl["email"] or "")
                    if veh: fiche.update(dict(veh))
            elif cle in ("email", "telephone"):
                cl = c.execute(f"SELECT * FROM clients WHERE compact({ 'telephone' if cle == 'telephone' else 'email' })=compact(?) ORDER BY id DESC LIMIT 1", (valeur,)).fetchone()
                if cl:
                    veh = c.execute("SELECT marque, modele, immatriculation AS immat, moteur, vin, kilometrage AS km FROM vehicules WHERE client_id=? ORDER BY id DESC LIMIT 1", (cl["id"],)).fetchone()
                    fiche = dict(client=cl["nom"], telephone=cl["telephone"], email=cl["email"] or "")
                    if veh: fiche.update(dict(veh))
        if not fiche:
            return
        # Une recherche ne remplace jamais un champ déjà renseigné par l'utilisateur.
        libelles = {"client":"client", "telephone":"téléphone", "email":"e-mail", "marque":"véhicule", "immat":"immatriculation", "moteur":"moteur", "vin":"VIN", "km":"kilométrage"}
        faits = []
        for k in ("client", "telephone", "email", "marque", "immat", "moteur", "vin", "km"):
            val = str(fiche.get(k, "") or "").strip()
            if val and k in self.champs and not self.champs[k].text.strip():
                self.champs[k].text = val
                self._auto_valeurs[k] = val
                faits.append(libelles[k])
        if faits:
            self.info_lbl.text = "Fiche reconnue — champs complétés : " + ", ".join(faits)

    @securise
    def ouvrir_controle_devis(self):
        """Contrôle local + propositions ligne par ligne; chaque application exige un clic."""
        lignes = self.lire_lignes()
        issues = controler_devis_local(lignes, self.champs["marque"].text, self.champs["km"].text)
        propositions = proposer_corrections_lignes(lignes, self.champs["marque"].text, self.champs["km"].text)

        boite = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(6))
        titre_lbl = etiquette(
            "Les valeurs proposées sont indicatives. Rien ne sera changé sans votre clic.",
            12, BLEU_FONCE, True, 48)
        boite.add_widget(titre_lbl)
        scroll = ScrollView(size_hint=(1, 1))
        contenu = GridLayout(cols=1, spacing=dp(7), padding=dp(3), size_hint_y=None)
        contenu.bind(minimum_height=contenu.setter("height"))
        scroll.add_widget(contenu)
        boite.add_widget(scroll)

        corrections_en_attente = []
        if not propositions:
            contenu.add_widget(etiquette(
                "Aucune correction automatique suggérée à partir de l'historique. "
                "Cela ne garantit pas que les prix et quantités soient exacts.",
                12, GRIS_TEXTE, False, 54))
        else:
            for proposition in propositions:
                idx = proposition["index"]
                ligne_widget = self.lignes[idx] if idx < len(self.lignes) else None
                bloc = BoxLayout(orientation="vertical", padding=dp(6), spacing=dp(4),
                                 size_hint_y=None)
                bloc.bind(minimum_height=bloc.setter("height"))
                bloc.add_widget(etiquette(
                    f"Ligne {idx+1} — {proposition['designation']}", 13, BLEU_FONCE, True, 28))
                for sug in proposition["suggestions"]:
                    champ = sug["champ"]
                    nom_champ = {"quantite": "Quantité", "prix": "Prix", "type": "Type",
                                 "designation": "Désignation"}[champ]

                    def fmt(v, champ=champ):
                        if champ == "quantite":
                            return nombre_txt(v)
                        return prix_affiche(v) if champ == "prix" else str(v)
                    nb = sug.get("references") or 0
                    label_txt = (f"{nom_champ} saisi(e) : {fmt(sug['actuel'])}  →  proposé(e) : {fmt(sug['propose'])}\n"
                                 f"{sug['raison']}" + (f" ({nb} références dans l'historique)" if nb else ""))
                    bloc.add_widget(etiquette_multi(label_txt, 11))
                    action = BoxLayout(size_hint_y=None, height=dp(38), spacing=dp(5))
                    # « APPLIQUER TOUTES » : prix et quantités fiables seulement (jamais les simples
                    # hypothèses d'orthographe ni les écarts légers)
                    if champ in ("prix", "quantite", "type") and sug.get("niveau") != "info":
                        corrections_en_attente.append((ligne_widget, champ, sug["propose"]))
                    btn_appliquer = bouton("APPLIQUER", VERT, 36)
                    btn_refuser = bouton("IGNORER", GRIS, 36)
                    action.add_widget(btn_appliquer)
                    action.add_widget(btn_refuser)
                    bloc.add_widget(action)

                    def appliquer(_btn, cible=ligne_widget, champ_cible=champ,
                                  valeur=sug["propose"], bouton_courant=btn_appliquer):
                        if cible is None:
                            return
                        # Une proposition n'est appliquée qu'après le clic explicite.
                        if champ_cible == "quantite":
                            cible.quantite.text = nombre_txt(valeur)
                        elif champ_cible == "prix":
                            cible.prix.text = nombre_txt(valeur)
                        elif champ_cible == "type":
                            cible.type_ligne.text = str(valeur)
                        else:
                            cible.designation.text = str(valeur)
                        cible.changement()
                        bouton_courant.text = "APPLIQUÉ"
                        bouton_courant.disabled = True

                    def ignorer(_btn, bouton_courant=btn_refuser, bouton_apply=btn_appliquer):
                        bouton_courant.text = "IGNORÉ"
                        bouton_courant.disabled = True
                        bouton_apply.disabled = True

                    btn_appliquer.bind(on_release=appliquer)
                    btn_refuser.bind(on_release=ignorer)
                contenu.add_widget(bloc)

        if issues:
            contenu.add_widget(etiquette("AUTRES ALERTES DU CONTRÔLE", 13, ORANGE, True, 28))
            for issue in issues[:30]:
                contenu.add_widget(etiquette_multi("• " + issue["message"], 11))

        actions = BoxLayout(size_hint_y=None, height=dp(44), spacing=dp(5))
        b_ia = bouton("RELIRE AVEC IA", BLEU, 42)
        b_lot = bouton("APPLIQUER TOUTES", VERT, 42)
        b_fermer = bouton("FERMER", GRIS, 42)
        actions.add_widget(b_ia)
        if corrections_en_attente:
            actions.add_widget(b_lot)
        actions.add_widget(b_fermer)

        def appliquer_tout(*_):
            appliquees = 0
            for cible, champ_cible, valeur in corrections_en_attente:
                if cible is None:
                    continue
                if champ_cible == "quantite":
                    cible.quantite.text = nombre_txt(valeur)
                elif champ_cible == "prix":
                    cible.prix.text = nombre_txt(valeur)
                elif champ_cible == "type":
                    cible.type_ligne.text = str(valeur)
                else:
                    continue
                cible.changement()
                appliquees += 1
            b_lot.text = "APPLIQUÉES" if appliquees else "RIEN À APPLIQUER"
            b_lot.disabled = True
            afficher_popup("Corrections appliquées", f"{appliquees} valeur(s) appliquée(s) au formulaire. Rien n'est enregistré tant que vous n'enregistrez pas le devis. Vérifiez chaque ligne.")

        if corrections_en_attente:
            b_lot.bind(on_release=appliquer_tout)
        boite.add_widget(actions)
        pop = Popup(title="Contrôle et corrections proposées", content=boite,
                    size_hint=(0.96, 0.92), auto_dismiss=False)

        def lancer(*_):
            if not ia_disponible():
                afficher_popup("Assistant IA", "Activez l'IA dans Paramètres et configurez la clé API.")
                return
            b_ia.disabled = True
            titre_lbl.text = "L'IA relit les lignes… aucune correction ne sera appliquée automatiquement."
            def travail():
                try:
                    res = ia_controler_devis(
                        self.lire_lignes(), self.champs["marque"].text,
                        self.champs["km"].text, self.champs["moteur"].text,
                        [i["message"] for i in issues])
                    texte = "\n\n".join("• " + str(x.get("message", "")) for x in res)
                    if not texte:
                        texte = "L'IA n'a pas relevé d'autre anomalie. Vérifiez tout de même les références et les prix."
                    Clock.schedule_once(lambda dt: afficher_texte("Résultat de la relecture IA", texte))
                except Exception as exc:
                    msg = str(exc)
                    Clock.schedule_once(lambda dt: afficher_popup("IA indisponible", msg))
                finally:
                    Clock.schedule_once(lambda dt: setattr(b_ia, "disabled", False))
            threading.Thread(target=travail, daemon=True).start()

        b_ia.bind(on_release=lancer)
        b_fermer.bind(on_release=lambda *_: pop.dismiss())
        pop.open()

    @securise
    def ouvrir_infos_client(self):
        client, immat = self.champs["client"].text.strip(), self.champs["immat"].text.strip()
        if not client and not immat:
            afficher_popup("Fiche / historique", "Saisissez un nom de client ou une immatriculation.")
            return
        boite = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(6))
        question = TextInput(hint_text="Question : quand les plaquettes ont-elles été changées ?", multiline=False, size_hint_y=None, height=dp(42), font_size=sp(13))
        boite.add_widget(question)
        zone = TexteDefilant(); zone.set(fiche_client_vehicule(client, immat)); boite.add_widget(zone)
        actions = BoxLayout(size_hint_y=None, height=dp(44), spacing=dp(5))
        b_h = bouton("HISTORIQUE", BLEU, 42); b_q = bouton("RÉPONDRE", BLEU_FONCE, 42); b_ia = bouton("DEMANDER À L'IA", BLEU, 42); b_f = bouton("FERMER", GRIS, 42)
        for b in (b_h, b_q, b_ia, b_f): actions.add_widget(b)
        boite.add_widget(actions)
        pop = Popup(title="Informations client / véhicule", content=boite, size_hint=(0.96, 0.92))
        def local(*_):
            km_form = int(prix_nombre(self.champs["km"].text))
            zone.set(repondre_question_historique(question.text, client, immat, km_form))
        def ia_q(*_):
            q = question.text.strip()
            if not q:
                zone.set("Écrivez d'abord une question.")
                return
            hors = repondre_question_historique(q, client, immat)
            if not ia_historique_autorise():
                zone.set("IA non utilisée sur l'historique. Paramètres : « IA activée » = Oui, "
                         "« IA peut lire l'historique » = Oui, et la clé API.\n\n" + hors)
                return
            km_form = int(prix_nombre(self.champs["km"].text))
            ctx = contexte_anonyme(client, immat, self.champs["marque"].text.strip(),
                                   self.champs["moteur"].text.strip(), km_form)
            zone.set(hors + "\n\n--- L'IA réfléchit... ---")

            def travail():
                try:
                    rep = ia_repondre(q, ctx)
                    Clock.schedule_once(lambda dt: zone.set(hors + "\n\n--- Réponse de l'IA ---\n"
                                                            + (rep or "L'IA n'a pas retourné de réponse.")))
                except Exception as exc:
                    msg = str(exc)
                    Clock.schedule_once(lambda dt: zone.set(hors + "\n\n--- IA indisponible : " + msg + " ---"))
            threading.Thread(target=travail, daemon=True).start()
        b_h.bind(on_release=lambda *_: zone.set(fiche_client_vehicule(client, immat) + "\n\n" + (historique_texte(client or None, immat or None) or "Aucun historique.")))
        b_q.bind(on_release=local); b_ia.bind(on_release=ia_q); b_f.bind(on_release=lambda *_: pop.dismiss()); question.bind(on_text_validate=local)
        pop.open()

    def lire_lignes(self):
        res = []
        for l in self.lignes:
            q, p = prix_nombre(l.quantite.text), prix_nombre(l.prix.text)
            res.append({"type": l.type_ligne.text, "designation": l.designation.text.strip(),
                        "quantite": q, "prix": p, "total": q * p})
        return res

    _totaux_suspendus = False

    def calculer_totaux(self):
        if self._totaux_suspendus:
            return None
        t = totaux(self.lire_lignes(), self.taux)
        if self.taux:
            self.total_general.text = f"TOTAL TTC : {prix_affiche(t['ttc'])}  (HT {prix_affiche(t['ht'])})"
        else:
            self.total_general.text = f"TOTAL DEVIS : {prix_affiche(t['ttc'])}"
        return t

    # -- enregistrement ----------------------------------------
    @securise
    def enregistrer(self, *args):
        d = {k: w.text.strip() for k, w in self.champs.items()}
        d["vehicule"] = d["marque"]
        if not d["client"] or not d["immat"]:
            afficher_popup("Validation", "Renseignez au moins le Client et l'Immatriculation.")
            return
        if not email_valide(d["email"]):
            afficher_popup("Validation", "L'adresse e-mail du client n'est pas valide.")
            return
        lignes = [l for l in self.lire_lignes() if l["designation"]]
        if not lignes:
            afficher_popup("Devis vide", "Ajoutez au moins une ligne avec une désignation.")
            return

        edition = self.devis_id is not None
        devis_id, _ = sauver_devis(d, lignes, self.devis_id, self.taux)
        chemin, doc = regenerer_pdf("Devis", devis_id)
        self.reinitialiser()
        self.apres_enregistrement(devis_id, doc, chemin, edition)

    def apres_enregistrement(self, devis_id, doc, chemin, edition):
        numero = numero_doc("DEV", devis_id, doc["date"])
        etat = f"mis à jour (révision {doc['version']})" if edition else "enregistré"
        msg = f"Devis {numero} {etat}\nTotal : {prix_affiche(doc['total'])}"
        # Envoi automatique du devis corrigé si activé dans Paramètres
        if edition and param("auto_envoi") == "Oui" and doc["email"]:
            envoyer_document("Devis", devis_id)
            return
        popup_actions("Devis enregistré", msg, [
            ("Envoyer par e-mail", VERT, lambda: envoyer_document("Devis", devis_id)),
            ("WhatsApp / Partager", ORANGE, lambda: partager_whatsapp("Devis", devis_id)),
            ("Voir le PDF", BLEU, (lambda: ouvrir_ou_partager(chemin)) if chemin else None),
            ("Fermer", GRIS, None)])


# ============================================================
# ÉCRAN DEVIS & FACTURES
# ============================================================

class _RemplissageProgressif:
    """Ajoute les fiches d'une liste par petits lots, image après image :
    l'écran reste fluide même avec 100 résultats (V12 créait tout d'un coup)."""

    LOT = 6
    _tache_remplissage = None
    _file_remplissage = ()
    _zone_remplissage = None
    _jeton = 0     # numéro de la dernière recherche : les résultats périmés sont ignorés

    def _arreter_remplissage(self):
        if self._tache_remplissage is not None:
            self._tache_remplissage.cancel()
            self._tache_remplissage = None
        self._file_remplissage = ()

    def _remplir(self, zone, fabriques):
        """fabriques = liste de fonctions sans argument qui créent chacune un widget."""
        self._arreter_remplissage()
        zone.clear_widgets()
        self._zone_remplissage = zone
        self._file_remplissage = list(reversed(fabriques))
        self._lot_remplissage(0)

    def _lot_remplissage(self, dt):
        self._tache_remplissage = None
        file = self._file_remplissage
        try:
            for _ in range(self.LOT):
                if not file:
                    return
                self._zone_remplissage.add_widget(file.pop()())
        except Exception as e:
            self._file_remplissage = ()
            afficher_popup("Erreur", str(e))
            return
        if file:
            self._tache_remplissage = Clock.schedule_once(self._lot_remplissage, 0)


class FacturesScreen(_RemplissageProgressif, Screen):

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        racine = BoxLayout(orientation="vertical", padding=dp(12), spacing=dp(8))
        racine.add_widget(titre("DEVIS & FACTURES"))
        self.champ = TextInput(hint_text="Rechercher : nom, plaque, VIN, date, impayé...", multiline=False,
                               size_hint_y=None, height=dp(44), font_size=sp(14))
        # Recherche temporisée : conserver la tâche sur l'écran, pas sur une méthode liée.
        self._recherche_tache = None
        self.champ.bind(text=self._texte_recherche_change)
        racine.add_widget(self.champ)
        b_avance = bouton("+ ENREGISTRER UNE AVANCE / UN PAIEMENT", ORANGE, 46)
        b_avance.bind(on_release=lambda *_: selectionner_facture_paiement(self.charger))
        racine.add_widget(b_avance)
        b_recap = bouton("PDF — RÉCAPITULATIF DES FACTURES EN COURS", VERT, 44)
        b_recap.bind(on_release=lambda *_: self.generer_recap())
        racine.add_widget(b_recap)
        self.zone = GridLayout(cols=1, spacing=dp(8), size_hint_y=None)
        self.zone.bind(minimum_height=self.zone.setter("height"))
        sv = ScrollView()
        sv.add_widget(self.zone)
        racine.add_widget(sv)
        racine.add_widget(bouton_retour(self))
        self.add_widget(racine)

    def on_enter(self):
        self.charger()

    def _texte_recherche_change(self, *_):
        """Programme la recherche après une courte pause et annule la tâche précédente."""
        try:
            if self._recherche_tache is not None:
                self._recherche_tache.cancel()
        except Exception:
            pass
        self._recherche_tache = Clock.schedule_once(self.charger, 0.30)

    def on_leave(self, *args):
        self._jeton += 1
        self._arreter_remplissage()

    @securise
    def charger(self, *args):
        a = analyser_recherche(self.champ.text)
        cats = categories_voulues(a, {"devis", "facture"})
        self._jeton += 1
        jeton = self._jeton

        def travail():
            try:
                # Afficher aussi les devis déjà facturés : ils restent des modèles réutilisables.
                devis = chercher_devis(a, 60) if "devis" in cats else []
                factures = chercher_factures(a, 60) if "facture" in cats else []
                erreur = None
            except Exception as e:
                devis, factures, erreur = [], [], e
            Clock.schedule_once(lambda dt: self._afficher(jeton, devis, factures, erreur))
        threading.Thread(target=travail, daemon=True).start()

    def _afficher(self, jeton, devis, factures, erreur):
        if jeton != self._jeton:
            return
        if erreur is not None:
            afficher_popup("Erreur", str(erreur))
            return
        fabriques = [lambda: etiquette("DEVIS ENREGISTRÉS — MODIFIER OU RÉUTILISER", 14, ORANGE, True, 30)]
        if not devis:
            fabriques.append(lambda: etiquette("Aucun devis trouvé. Essayez une recherche moins précise.", 12, GRIS, False, 24))
        fabriques.extend(lambda d=d: self._carte_devis(d) for d in devis)
        fabriques.append(lambda: etiquette("FACTURES", 14, ORANGE, True, 30))
        if not factures:
            fabriques.append(lambda: etiquette("Aucune facture.", 12, GRIS, False, 24))
        fabriques.extend(lambda f=f: self._carte_facture(f) for f in factures)
        self._remplir(self.zone, fabriques)

    def _carte_devis(self, d):
        i = d["id"]
        rev = f" (rév. {d['version']})" if (d["version"] or 1) > 1 else ""
        statut = str(d["statut"] or "En attente")
        sous_titre = f"{d['vehicule']} ({d['immatriculation']}) | {d['date_devis']} | {prix_affiche(d['total'])} | {statut}"
        actions_devis = [("Réutiliser", VERT, lambda x, i=i: self.reutiliser(i)),
                         ("PDF", BLEU_FONCE, lambda x, i=i: voir_pdf("Devis", i)),
                         ("E-mail", ORANGE, lambda x, i=i: envoyer_document("Devis", i)),
                         ("WhatsApp", ORANGE, lambda x, i=i: partager_whatsapp("Devis", i))]
        if statut != "Facturé":
            actions_devis.insert(0, ("Modifier", BLEU, lambda x, i=i: self.modifier(i)))
            actions_devis.append(("Facturer", VERT, lambda x, i=i: self.facturer(i)))
        return carte(f"{numero_doc('DEV', i, d['date_devis'])}{rev} - {d['client']}", sous_titre, actions_devis)

    def _carte_facture(self, f):
        i = f["id"]
        reste = f["reste"] or 0
        etat = "PAYÉE" if reste < 1 else f"Reste {prix_affiche(reste)}"
        return carte(
            f"{numero_doc('FAC', i, f['date_facture'])} - {f['client']}",
            f"{f['vehicule']} ({f['immatriculation']}) | {prix_affiche(f['total'])} | {etat}",
            [("PDF", BLEU_FONCE, lambda x, i=i: voir_pdf("Facture", i)),
             ("E-mail", ORANGE, lambda x, i=i: envoyer_document("Facture", i)),
             ("WhatsApp", ORANGE, lambda x, i=i: partager_whatsapp("Facture", i)),
             ("AJOUTER AVANCE", VERT, lambda x, i=i: formulaire_paiement(i, self.charger))])

    @securise
    def generer_recap(self):
        chemin = generer_pdf_recap_factures()
        popup_actions("Récapitulatif prêt", "Le PDF des factures en cours et des avances encaissées depuis aujourd'hui a été créé.", [
            ("Ouvrir / partager le PDF", VERT, lambda: ouvrir_ou_partager(chemin)),
            ("Fermer", GRIS, None)])

    @securise
    def modifier(self, devis_id):
        ecran = self.manager.get_screen("devis")
        ecran.charger(devis_id)
        self.manager.current = "devis"

    @securise
    def reutiliser(self, devis_id):
        """Charge un ancien devis en nouveau brouillon, sans écraser l'ancien."""
        ecran = self.manager.get_screen("devis")
        ecran.reutiliser(devis_id)
        self.manager.current = "devis"

    def facturer(self, devis_id):
        @securise
        def go():
            fid = facturer_devis(devis_id)
            _, doc = regenerer_pdf("Facture", fid)
            self.charger()
            popup_actions("Facture créée",
                          f"Facture {numero_doc('FAC', fid, doc['date'])}\nTotal : {prix_affiche(doc['total'])}", [
                              ("Envoyer par e-mail", VERT, lambda: envoyer_document("Facture", fid)),
                              ("WhatsApp / Partager", ORANGE, lambda: partager_whatsapp("Facture", fid)),
                              ("Fermer", GRIS, None)])

        popup_actions("Confirmer", "Générer la facture ?\nUne facture émise ne se modifie plus.", [
            ("Oui, facturer", VERT, go), ("Annuler", GRIS, None)])


# ============================================================
# LISTES (clients, véhicules, historique des prix, recherche)
# ============================================================

# ---- Analyse de la saisie : mots, dates, type, statut ----------------------

MOIS = {"janvier": 1, "fevrier": 2, "mars": 3, "avril": 4, "mai": 5, "juin": 6, "juillet": 7,
        "aout": 8, "septembre": 9, "octobre": 10, "novembre": 11, "decembre": 12}
TYPES = {"client": "client", "clients": "client", "vehicule": "vehicule", "vehicules": "vehicule",
         "voiture": "vehicule", "voitures": "vehicule", "devis": "devis",
         "facture": "facture", "factures": "facture"}
STATUTS = {"impaye": "impaye", "impayee": "impaye", "impayes": "impaye", "impayees": "impaye",
           "paye": "paye", "payee": "paye", "payes": "paye", "payees": "paye",
           "attente": "attente", "annule": "annule", "annulee": "annule", "annulees": "annule"}
SENS = {"recette": "R", "recettes": "R", "depense": "D", "depenses": "D"}
MOTS_VIDES = {"du", "au", "le", "la", "les", "de", "des", "ce", "cette", "en", "et", "a", "l", "d"}


def _plage_mois(an, mois):
    return f"{an}-{mois:02d}-01", f"{an}-{mois:02d}-{calendar.monthrange(an, mois)[1]:02d}"


def analyser_recherche(texte):
    """Comprend : 1921tbh, tsiferana, terracan, VIN, 05/10/2026, 10/2026, octobre 2026,
    du 01/10/2026 au 15/10/2026, hier, aujourd'hui, semaine, mois, année 2025, impayé, devis..."""
    t = str(texte or "")
    r = {"mots": [], "debut": None, "fin": None, "types": set(), "statuts": set(), "sens": set()}
    auj = datetime.now().date()

    iso = []
    for j, m_, a_ in re.findall(r"\b(\d{1,2})[/.\-](\d{1,2})[/.\-](\d{4})\b", t):
        try:
            iso.append(datetime(int(a_), int(m_), int(j)).strftime("%Y-%m-%d"))
        except ValueError:
            pass
    t = re.sub(r"\b\d{1,2}[/.\-]\d{1,2}[/.\-]\d{4}\b", " ", t)
    if iso:
        r["debut"], r["fin"] = min(iso), max(iso)
    else:
        m = re.search(r"\b(\d{1,2})[/.]((?:19|20)\d{2})\b", t)
        if m and 1 <= int(m.group(1)) <= 12:
            r["debut"], r["fin"] = _plage_mois(int(m.group(2)), int(m.group(1)))
            t = t.replace(m.group(0), " ")

    tokens = t.split()
    i = 0
    while i < len(tokens):
        brut = tokens[i]
        n = compacter(brut)
        suivant = tokens[i + 1] if i + 1 < len(tokens) else ""
        s_n = compacter(suivant)
        annee_suiv = bool(re.fullmatch(r"(19|20)\d{2}", suivant))
        libre = r["debut"] is None
        if n in MOIS and libre:
            an = int(suivant) if annee_suiv else auj.year
            r["debut"], r["fin"] = _plage_mois(an, MOIS[n])
            i += 1 if annee_suiv else 0
        elif n in ("annee", "an") and annee_suiv and libre:
            r["debut"], r["fin"] = f"{suivant}-01-01", f"{suivant}-12-31"
            i += 1
        elif n == "annee" and libre:
            r["debut"], r["fin"] = f"{auj.year}-01-01", f"{auj.year}-12-31"
        elif n == "aujourdhui" and libre:
            r["debut"] = r["fin"] = auj.strftime("%Y-%m-%d")
        elif n == "hier" and libre:
            r["debut"] = r["fin"] = (auj - timedelta(days=1)).strftime("%Y-%m-%d")
        elif n == "semaine" and libre:
            r["debut"] = (auj - timedelta(days=auj.weekday())).strftime("%Y-%m-%d")
            r["fin"] = auj.strftime("%Y-%m-%d")
        elif n == "mois" and libre:
            if s_n in ("dernier", "precedent"):
                dernier = auj.replace(day=1) - timedelta(days=1)
                r["debut"], r["fin"] = _plage_mois(dernier.year, dernier.month)
                i += 1
            else:
                r["debut"], r["fin"] = _plage_mois(auj.year, auj.month)
        elif n in TYPES:
            r["types"].add(TYPES[n])
        elif n in STATUTS:
            r["statuts"].add(STATUTS[n])
        elif n in SENS:
            r["sens"].add(SENS[n])
        elif n in MOTS_VIDES or not n:
            pass
        else:
            r["mots"].append(re.sub(r"[%_]", "", brut))
        i += 1
    return r


def description_recherche(a):
    parts = []
    if a["mots"]:
        parts.append("Mots : " + ", ".join(a["mots"]))
    if a["debut"]:
        d1, d2 = fr_depuis_iso(a["debut"]), fr_depuis_iso(a["fin"])
        parts.append("Date : " + (d1 if d1 == d2 else f"du {d1} au {d2}"))
    if a["types"]:
        parts.append("Type : " + ", ".join(sorted(a["types"])))
    if a["statuts"]:
        parts.append("Statut : " + ", ".join(sorted(a["statuts"])))
    return "   |   ".join(parts)


def categories_voulues(a, cats):
    cats = set(cats)
    if a["types"]:
        cats &= a["types"]
    if a["statuts"] & {"impaye", "paye"}:
        cats &= {"facture"}
    if "attente" in a["statuts"]:
        cats &= {"devis"}
    return cats


# ---- Construction des requêtes SQL ---------------------------------------

ISO_D = "(substr(d.date_devis,7,4)||'-'||substr(d.date_devis,4,2)||'-'||substr(d.date_devis,1,2))"
ISO_F = "(substr(f.date_facture,7,4)||'-'||substr(f.date_facture,4,2)||'-'||substr(f.date_facture,1,2))"
ISO_H = "(substr(h.date_prix,7,4)||'-'||substr(h.date_prix,4,2)||'-'||substr(h.date_prix,1,2))"
RESTE = ("(f.total - COALESCE((SELECT SUM(montant) FROM paiements p "
         "WHERE p.facture_id=f.id AND p.annule=0),0))")

# norm = texte (sans accents) ; compact = codes (plaque, VIN, téléphone, n° de document)
SPEC_DEVIS = {
    "norm": ["d.client", "d.vehicule", "d.statut"],
    "compact": ["d.immatriculation", "('DEV'||substr(d.date_devis,7,4)||printf('%04d', d.id))"],
    "exists": [
        {"de": "vehicules v", "ext": "compact(d.immatriculation)", "int": "compact(v.immatriculation)",
         "compact": ["v.vin", "v.moteur"]},
        {"de": "clients cl", "ext": "norm(d.client)", "int": "norm(cl.nom)",
         "norm": ["cl.email"], "compact": ["cl.telephone"]}]}
SPEC_FACTURES = {
    "norm": ["f.client", "f.vehicule"],
    "compact": ["f.immatriculation", "('FAC'||substr(f.date_facture,7,4)||printf('%04d', f.id))"],
    "exists": [
        {"de": "vehicules v", "ext": "compact(f.immatriculation)", "int": "compact(v.immatriculation)",
         "compact": ["v.vin", "v.moteur"]},
        {"de": "clients cl", "ext": "norm(f.client)", "int": "norm(cl.nom)",
         "norm": ["cl.email"], "compact": ["cl.telephone"]}]}
SPEC_CLIENTS = {
    "norm": ["c.nom", "c.email", "c.adresse"], "compact": ["c.telephone"],
    "exists": [{"de": "vehicules v", "ext": "c.id", "int": "v.client_id", "norm": ["v.marque", "v.modele"],
                "compact": ["v.immatriculation", "v.vin", "v.moteur"]}]}
SPEC_VEHICULES = {
    "norm": ["v.marque", "v.modele", "c.nom", "c.email"],
    "compact": ["v.immatriculation", "v.vin", "v.moteur", "c.telephone"]}
SPEC_PRIX = {"norm": ["h.designation", "h.marque", "h.modele"]}


def condition_mot(mot, spec):
    """Un mot doit se retrouver dans AU MOINS une colonne ; tous les mots doivent être trouvés."""
    n, k = f"%{normaliser(mot)}%", compacter(mot)
    k = f"%{k}%" if k else None
    ors, p = [], []
    for col in spec.get("norm", []):
        ors.append(f"norm({col}) LIKE ?")
        p.append(n)
    if k:
        for col in spec.get("compact", []):
            ors.append(f"compact({col}) LIKE ?")
            p.append(k)
    for ex in spec.get("exists", []):
        sub = [f"norm({c}) LIKE ?" for c in ex.get("norm", [])]
        pp = [n] * len(sub)
        if k:
            sub += [f"compact({c}) LIKE ?" for c in ex.get("compact", [])]
            pp += [k] * len(ex.get("compact", []))
        if sub:
            # IN (sous-requête NON corrélée) : calculée une seule fois, au lieu d'un balayage
            # complet de la table liée pour chaque ligne (EXISTS corrélé = O(n x m)).
            ors.append(f"{ex['ext']} IN (SELECT {ex['int']} FROM {ex['de']} WHERE " + " OR ".join(sub) + ")")
            p += pp
    return "(" + " OR ".join(ors) + ")", p


def _conditions(spec, a):
    where, params = [], []
    for mot in a["mots"]:
        sql, p = condition_mot(mot, spec)
        where.append(sql)
        params += p
    return where, params


def _executer(select, where, params, ordre, limite):
    sql = select + (" WHERE " + " AND ".join(where) if where else "") + f" ORDER BY {ordre} LIMIT ?"
    with db() as c:
        return c.execute(sql, params + [limite]).fetchall()


def chercher_devis(a, limite=40, en_cours=False):
    where, params = _conditions(SPEC_DEVIS, a)
    if a["debut"]:
        where.append(f"{ISO_D} BETWEEN ? AND ?")
        params += [a["debut"], a["fin"]]
    if en_cours or "attente" in a["statuts"]:
        where.append("d.statut != 'Facturé'")
    return _executer("SELECT d.* FROM devis d", where, params, "d.id DESC", limite)


def chercher_factures(a, limite=40):
    where, params = _conditions(SPEC_FACTURES, a)
    if a["debut"]:
        where.append(f"{ISO_F} BETWEEN ? AND ?")
        params += [a["debut"], a["fin"]]
    if "impaye" in a["statuts"]:
        where.append(f"{RESTE} > 0.5")
    if "paye" in a["statuts"]:
        where.append(f"{RESTE} <= 0.5")
    return _executer(f"SELECT f.*, {RESTE} AS reste FROM factures f", where, params, "f.id DESC", limite)


LIMITE_PIECES = 60   # nombre maximal de lignes « pièces » affichées (chaque ligne = une fiche à l'écran)


def chercher_pieces_documents(texte, limite=LIMITE_PIECES):
    """Recherche une pièce dans les lignes historiques de devis ET factures.

    Les mots saisis peuvent correspondre à la désignation, au modèle du véhicule,
    à l'immatriculation, au client ou au numéro du document. La comparaison ignore
    casse et accents. V13 : le filtrage, le tri (date réelle, du plus récent au plus
    ancien) et la limite sont faits par SQLite ; seules les lignes retenues
    arrivent en Python (V12 chargeait TOUTES les lignes de la base à chaque frappe)."""
    mots = [normaliser(x) for x in re.findall(r"[\w-]+", str(texte or ""), re.UNICODE)]
    mots = [m for m in mots if m and m not in MOTS_VIDES and m not in TYPES]
    if not mots:
        return []
    interne = """SELECT 'Devis' AS type_doc, d.id AS doc_id, d.client AS client,
                    d.vehicule AS vehicule, d.immatriculation AS immatriculation,
                    d.date_devis AS date_doc, d.total AS total_doc, d.statut AS statut,
                    l.designation AS designation, l.type_ligne AS type_ligne,
                    l.quantite AS quantite, l.prix_unitaire AS prix_unitaire,
                    l.total AS total_ligne, {iso_d} AS iso,
                    norm(COALESCE(l.designation,'')||' '||COALESCE(l.type_ligne,'')) AS hl,
                    norm(COALESCE(d.vehicule,'')||' '||COALESCE(d.immatriculation,'')||' '||
                         COALESCE(d.client,'')||' '||COALESCE(d.date_devis,'')||' '||d.id) AS hh
             FROM lignes_devis l JOIN devis d ON d.id=l.devis_id
             UNION ALL
             SELECT 'Facture', f.id, f.client, f.vehicule, f.immatriculation,
                    f.date_facture, f.total, 'Facturée',
                    l.designation, l.type_ligne, l.quantite, l.prix_unitaire, l.total,
                    {iso_f},
                    norm(COALESCE(l.designation,'')||' '||COALESCE(l.type_ligne,'')),
                    norm(COALESCE(f.vehicule,'')||' '||COALESCE(f.immatriculation,'')||' '||
                         COALESCE(f.client,'')||' '||COALESCE(f.date_facture,'')||' '||f.id)
             FROM lignes_facture l JOIN factures f ON f.id=l.facture_id""".format(iso_d=ISO_D, iso_f=ISO_F)
    # Tous les mots doivent apparaître quelque part (désignation, véhicule, client, document...).
    conditions = " AND ".join("(instr(hl, ?) > 0 OR instr(hh, ?) > 0)" for _ in mots)
    params = [m for m in mots for _ in (0, 1)]
    sql = ("SELECT type_doc, doc_id, client, vehicule, immatriculation, date_doc, total_doc, statut, "
           "designation, type_ligne, quantite, prix_unitaire, total_ligne FROM (" + interne + ") "
           "WHERE " + conditions + " ORDER BY iso DESC, doc_id DESC LIMIT ?")
    with db() as c:
        return [dict(r) for r in c.execute(sql, params + [int(limite)]).fetchall()]


def chercher_clients(a, limite=40, recents=False):
    where, params = _conditions(SPEC_CLIENTS, a)
    if a["debut"]:  # clients ayant eu un devis sur la période
        where.append(f"norm(c.nom) IN (SELECT norm(d.client) FROM devis d "
                     f"WHERE {ISO_D} BETWEEN ? AND ?)")
        params += [a["debut"], a["fin"]]
    return _executer("SELECT c.id, c.nom, c.telephone, c.email, "
                     "(SELECT COUNT(*) FROM vehicules v WHERE v.client_id=c.id) AS nb FROM clients c",
                     where, params, "c.id DESC" if recents else "norm(c.nom)", limite)


def chercher_vehicules(a, limite=40, recents=False):
    where, params = _conditions(SPEC_VEHICULES, a)
    if a["debut"]:
        where.append(f"compact(v.immatriculation) IN (SELECT compact(d.immatriculation) FROM devis d "
                     f"WHERE {ISO_D} BETWEEN ? AND ?)")
        params += [a["debut"], a["fin"]]
    return _executer("SELECT v.*, c.nom AS proprietaire, c.telephone AS tel FROM vehicules v "
                     "LEFT JOIN clients c ON c.id = v.client_id",
                     where, params, "v.id DESC" if recents else "norm(v.marque)", limite)


def donnees_historique(f):
    a = analyser_recherche(f)
    where, params = _conditions(SPEC_PRIX, a)
    if a["debut"]:
        where.append(f"{ISO_H} BETWEEN ? AND ?")
        params += [a["debut"], a["fin"]]
    rows = _executer("SELECT h.* FROM historique_prix h", where, params, "h.id DESC", 100)
    return "\n\n".join(f"{r['designation']} : {prix_affiche(r['prix'])}\n    {r['marque'] or '-'} ({r['date_prix']})"
                       for r in rows)


def filtrer_journal(lignes, a):
    """Recherche dans le journal : libellé, catégorie, tiers, pièce, mode, montant, date."""
    res = []
    for l in lignes:
        if a["debut"] and not (a["debut"] <= l["date"] <= a["fin"]):
            continue
        if a["sens"] and l["sens"] not in a["sens"]:
            continue
        if "annule" in a["statuts"] and not l["annule"]:
            continue
        meule = " ".join([l["cat"], l["lib"], l["tiers"], l["piece"], l["mode"],
                          nombre_txt(l["montant"]), fr_depuis_iso(l["date"])])
        n, k = normaliser(meule), compacter(meule)
        if all(normaliser(m) in n or (compacter(m) and compacter(m) in k) for m in a["mots"]):
            res.append(l)
    return res


# ---- Fiches : pré-remplissage et historique -----------------------------

def donnees_prefill(client_id=None, vehicule_id=None):
    with db() as c:
        v = None
        if vehicule_id:
            v = c.execute("SELECT * FROM vehicules WHERE id=?", (vehicule_id,)).fetchone()
            client_id = v["client_id"] if v else client_id
        cl = c.execute("SELECT * FROM clients WHERE id=?", (client_id,)).fetchone() if client_id else None
        if v is None and client_id:
            v = c.execute("SELECT * FROM vehicules WHERE client_id=? ORDER BY id DESC LIMIT 1",
                          (client_id,)).fetchone()
    d = {}
    if cl:
        d.update(client=cl["nom"], telephone=cl["telephone"], email=cl["email"] or "")
    if v:
        d.update(marque=v["marque"], immat=v["immatriculation"], moteur=v["moteur"],
                 vin=v["vin"], km=v["kilometrage"])
    return d


def historique_texte(client=None, immat=None):
    """Historique des réparations : un bloc par devis, avec ses lignes et sa facture."""
    with db() as c:
        if immat:
            devis = c.execute("SELECT * FROM devis WHERE compact(immatriculation)=compact(?) ORDER BY id DESC",
                              (immat,)).fetchall()
        else:
            devis = c.execute("SELECT * FROM devis WHERE norm(client)=norm(?) ORDER BY id DESC",
                              (client,)).fetchall()
        blocs = []
        for d in devis:
            travaux = [f"{l['designation']}" + (f" x{nombre_txt(l['quantite'])}" if l["quantite"] != 1 else "")
                       for l in c.execute("SELECT * FROM lignes_devis WHERE devis_id=? ORDER BY numero",
                                          (d["id"],))]
            f = c.execute(f"SELECT f.id, f.date_facture, {RESTE} AS reste FROM factures f "
                          f"WHERE f.devis_id=?", (d["id"],)).fetchone()
            etat = d["statut"]
            if f:
                etat = (f"Facturé ({numero_doc('FAC', f['id'], f['date_facture'])}, "
                        + ("payée" if f["reste"] < 1 else f"reste {prix_affiche(f['reste'])}") + ")")
            titre_b = f"{numero_doc('DEV', d['id'], d['date_devis'])} | {d['date_devis']} | {prix_affiche(d['total'])}"
            if not immat:
                titre_b += f" | {d['vehicule']} ({d['immatriculation']})"
            blocs.append(f"{titre_b} | {etat}\n    " + ("; ".join(travaux) or "-"))
    return "\n\n".join(blocs)


def afficher_texte(titre_txt, texte):
    boite = BoxLayout(orientation="vertical", spacing=dp(6), padding=dp(6))
    zone = TexteDefilant()
    zone.set(texte)
    boite.add_widget(zone)
    pop = Popup(title=titre_txt, content=boite, size_hint=(0.95, 0.85))
    b = bouton("FERMER", BLEU_FONCE, 44)
    b.bind(on_release=lambda x: pop.dismiss())
    boite.add_widget(b)
    pop.open()


@securise
def afficher_historique(client=None, immat=None):
    afficher_texte(f"HISTORIQUE - {immat or client}",
                   historique_texte(client, immat) or "Aucun devis pour le moment.")


_TACHES_PLANIFIEES = {}


def planifier(fn, delai=0.3):
    """Attend la fin de la frappe avant de lancer la recherche (fluide sur téléphone).

    V13 : fonctionne aussi avec une méthode liée (planifier(self.rafraichir)). En V12,
    poser un attribut sur une méthode liée levait une AttributeError à chaque frappe."""
    cle = (id(getattr(fn, "__self__", None)), getattr(fn, "__func__", fn))
    ancienne = _TACHES_PLANIFIEES.pop(cle, None)
    if ancienne is not None:
        ancienne.cancel()

    def lancer(dt):
        _TACHES_PLANIFIEES.pop(cle, None)
        fn()
    _TACHES_PLANIFIEES[cle] = Clock.schedule_once(lancer, delai)



class ResultatsScreen(_RemplissageProgressif, Screen):
    """Barre de recherche intelligente + résultats sous forme de fiches actionnables."""

    NOMS = {"Clients": "client", "Véhicules": "vehicule", "Devis": "devis", "Factures": "facture"}

    def __init__(self, titre_txt, categories, **kwargs):
        super().__init__(**kwargs)
        self.categories = set(categories)
        racine = BoxLayout(orientation="vertical", padding=dp(12), spacing=dp(6))
        racine.add_widget(titre(titre_txt))
        self.champ = TextInput(hint_text="Pièce + modèle : rotule direction Galloper, rotule Duster...", multiline=False,
                               size_hint_y=None, height=dp(44), font_size=sp(14))
        # Debounce stable : conserver l'événement sur l'instance de l'écran.
        # Ne pas utiliser planifier(self.rechercher), car chaque accès à une
        # méthode liée crée un nouvel objet et empêche l'annulation fiable.
        self._recherche_tache = None
        self.champ.bind(text=self._texte_recherche_change)
        racine.add_widget(self.champ)
        self.filtre = None
        if len(self.categories) > 1:
            self.filtre = Spinner(text="Tout", values=("Tout",) + tuple(self.NOMS),
                                  size_hint_y=None, height=dp(38))
            self.filtre.bind(text=lambda *a: self.rechercher())
            racine.add_widget(self.filtre)
        self.info = etiquette("", 11, GRIS, False, 22)
        racine.add_widget(self.info)
        self.zone = GridLayout(cols=1, spacing=dp(8), size_hint_y=None)
        self.zone.bind(minimum_height=self.zone.setter("height"))
        sv = ScrollView()
        sv.add_widget(self.zone)
        racine.add_widget(sv)
        racine.add_widget(bouton_retour(self))
        self.add_widget(racine)

    def _texte_recherche_change(self, instance, valeur):
        """Programme une recherche différée sans fermer ni recréer le champ."""
        if self._recherche_tache is not None:
            self._recherche_tache.cancel()
        self._recherche_tache = Clock.schedule_once(self._executer_recherche_differee, 0.35)

    def _executer_recherche_differee(self, dt):
        self._recherche_tache = None
        # Le champ garde son texte et son focus ; seuls les résultats sont rafraîchis.
        self.rechercher()

    def on_leave(self, *args):
        if self._recherche_tache is not None:
            self._recherche_tache.cancel()
            self._recherche_tache = None
        self._jeton += 1                 # ignore une recherche encore en cours
        self._arreter_remplissage()

    def on_enter(self):
        self.rechercher()

    @securise
    def rechercher(self, *args):
        texte_recherche = self.champ.text
        avait_focus = self.champ.focus
        a = analyser_recherche(texte_recherche)
        if len(self.categories) > 1:
            cats = set(self.categories)
            if self.filtre is not None and self.filtre.text != "Tout":
                cats = {self.NOMS[self.filtre.text]}
            cats = categories_voulues(a, cats)
        else:
            cats = set(self.categories)
        recents = not (a["mots"] or a["debut"] or a["types"] or a["statuts"])
        limite = 8 if recents else 40
        self.info.text = ("Recherchez aussi une pièce dans les anciens devis/factures : rotule direction Galloper, rotule Duster..."
                          if recents else description_recherche(a))
        # V13 : les requêtes tournent dans un thread (chaque appel db() ouvre sa propre
        # connexion) ; l'interface reste réactive pendant la frappe.
        self._jeton += 1
        jeton = self._jeton

        def travail():
            try:
                sections, erreur = self._collecter(a, cats, recents, limite, texte_recherche), None
            except Exception as e:
                sections, erreur = [], e
            Clock.schedule_once(lambda dt: self._afficher(jeton, sections, erreur, avait_focus))
        threading.Thread(target=travail, daemon=True).start()

    def _collecter(self, a, cats, recents, limite, texte_recherche):
        """Exécute les requêtes (thread de fond) : aucun widget n'est touché ici."""
        sections = []
        if "client" in cats:
            sections.append(("CLIENTS", chercher_clients(a, limite, recents), self._carte_client))
        if "vehicule" in cats:
            sections.append(("VÉHICULES", chercher_vehicules(a, limite, recents), self._carte_vehicule))
        if "devis" in cats:
            sections.append(("DEVIS", chercher_devis(a, limite), self._carte_devis))
        if "facture" in cats:
            sections.append(("FACTURES", chercher_factures(a, limite), self._carte_facture))
        # Recherche transversale des pièces proposées dans les anciens devis/factures.
        # Affichée même si l'utilisateur cherche depuis l'écran global RECHERCHE.
        if a["mots"]:
            sections.append(("PIÈCES DÉJÀ PROPOSÉES DANS LES DEVIS / FACTURES",
                             chercher_pieces_documents(texte_recherche, LIMITE_PIECES),
                             self._carte_piece_historique))
        return sections

    def _afficher(self, jeton, sections, erreur, avait_focus):
        if jeton != self._jeton:         # une recherche plus récente a été lancée
            return
        if erreur is not None:
            afficher_popup("Erreur", str(erreur))
            return
        fabriques = []
        for titre_txt, rows, fabrique in sections:
            if rows:
                fabriques.append(lambda t=f"{titre_txt} ({len(rows)})": etiquette(t, 14, ORANGE, True, 30))
                fabriques.extend(lambda r=r, f=fabrique: f(r) for r in rows)
        if not fabriques:
            fabriques.append(lambda: etiquette("Aucun résultat.", 13, GRIS, False, 30))
        self._remplir(self.zone, fabriques)
        if avait_focus:
            self.champ.focus = True

    # -- fiches ---------------------------------------------------
    def _carte_piece_historique(self, r):
        typ = r["type_doc"]
        i = r["doc_id"]
        prefixe = "DEV" if typ == "Devis" else "FAC"
        numero = numero_doc(prefixe, i, r["date_doc"])
        detail = (f"{r['designation']} | Qté : {r['quantite']:g} | "
                  f"PU : {prix_affiche(r['prix_unitaire'])} | Ligne : {prix_affiche(r['total_ligne'])}")
        sous = (f"{typ} {numero} | {r['client']} | {r['vehicule']} ({r['immatriculation']}) | "
                f"{r['date_doc']} | Total document : {prix_affiche(r['total_doc'])} | {detail}")
        return carte(f"{r['designation']} — {r['vehicule']} — {typ} {numero}", sous,
                     [("Voir PDF", BLEU_FONCE, lambda x, i=i, typ=typ: voir_pdf(typ, i)),
                      ("WhatsApp", ORANGE, lambda x, i=i, typ=typ: partager_whatsapp(typ, i))])

    def _carte_client(self, r):
        return carte(r["nom"], f"Tél {r['telephone'] or '-'} | {r['email'] or '-'} | {r['nb']} véhicule(s)",
                     [("Historique", BLEU_FONCE, lambda x, n=r["nom"]: afficher_historique(client=n)),
                      ("Nouveau devis", VERT, lambda x, i=r["id"]: self.nouveau_devis(client_id=i))])

    def _carte_vehicule(self, r):
        return carte(f"{r['marque'] or '-'} - {r['immatriculation']}",
                     f"{r['kilometrage'] or '-'} km | VIN {r['vin'] or '-'} | {r['proprietaire'] or '-'}",
                     [("Historique", BLEU_FONCE, lambda x, m=r["immatriculation"]: afficher_historique(immat=m)),
                      ("Nouveau devis", VERT, lambda x, i=r["id"]: self.nouveau_devis(vehicule_id=i))])

    def _carte_devis(self, d):
        i = d["id"]
        rev = f" (rév. {d['version']})" if (d["version"] or 1) > 1 else ""
        actions = []
        if d["statut"] != "Facturé":
            actions.append(("Modifier", BLEU, lambda x, i=i: self.modifier(i)))
        actions += [("PDF", BLEU_FONCE, lambda x, i=i: voir_pdf("Devis", i)),
                    ("E-mail", ORANGE, lambda x, i=i: envoyer_document("Devis", i)),
                    ("WhatsApp", ORANGE, lambda x, i=i: partager_whatsapp("Devis", i))]
        return carte(f"{numero_doc('DEV', i, d['date_devis'])}{rev} - {d['client']}",
                     f"{d['vehicule']} ({d['immatriculation']}) | {d['date_devis']} | "
                     f"{prix_affiche(d['total'])} | {d['statut']}", actions)

    def _carte_facture(self, f):
        i = f["id"]
        reste = f["reste"] or 0
        etat = "PAYÉE" if reste < 1 else f"Reste {prix_affiche(reste)}"
        return carte(f"{numero_doc('FAC', i, f['date_facture'])} - {f['client']}",
                     f"{f['vehicule']} ({f['immatriculation']}) | {f['date_facture']} | "
                     f"{prix_affiche(f['total'])} | {etat}",
                     [("PDF", BLEU_FONCE, lambda x, i=i: voir_pdf("Facture", i)),
                      ("E-mail", ORANGE, lambda x, i=i: envoyer_document("Facture", i)),
                      ("WhatsApp", ORANGE, lambda x, i=i: partager_whatsapp("Facture", i)),
                      ("Paiements", VERT if reste >= 1 else GRIS,
                       lambda x, i=i: formulaire_paiement(i, self.rechercher))])

    @securise
    def modifier(self, devis_id):
        self.manager.get_screen("devis").charger(devis_id)
        self.manager.current = "devis"

    @securise
    def nouveau_devis(self, client_id=None, vehicule_id=None):
        self.manager.get_screen("devis").preremplir(donnees_prefill(client_id, vehicule_id))
        self.manager.current = "devis"


class ListeScreen(Screen):

    def __init__(self, titre_txt, fonction, recherche=False, **kwargs):
        super().__init__(**kwargs)
        self.fonction = fonction
        racine = BoxLayout(orientation="vertical", padding=dp(15), spacing=dp(8))
        racine.add_widget(titre(titre_txt))
        self.champ = None
        if recherche:
            self.champ = TextInput(hint_text="Ex: filtre toyota octobre 2026", multiline=False,
                                   size_hint_y=None, height=dp(42))
            self.champ.bind(text=lambda *a: self._planifier_rafraichir())
            racine.add_widget(self.champ)
        self.texte = TexteDefilant()
        racine.add_widget(self.texte)
        racine.add_widget(bouton_retour(self))
        self.add_widget(racine)

    def on_enter(self):
        self.rafraichir()

    _tache_rafraichir = None

    def _planifier_rafraichir(self):
        """Attend la fin de la frappe (sinon une requête + un rendu de texte à chaque lettre)."""
        if self._tache_rafraichir is not None:
            self._tache_rafraichir.cancel()
        self._tache_rafraichir = Clock.schedule_once(lambda dt: self.rafraichir(), 0.3)

    def rafraichir(self):
        filtre = self.champ.text.strip() if self.champ else ""
        try:
            self.texte.set(self.fonction(filtre) or "Aucun résultat.")
        except Exception as e:
            self.texte.set(f"Erreur : {e}")


# ============================================================
# JOURNAL ET BILAN (interface)
# ============================================================

def _champ(hint, texte="", **kw):
    return TextInput(text=texte, hint_text=hint, multiline=False, font_size=sp(13),
                     size_hint_y=None, height=dp(42), **kw)


def _spinner(valeurs, texte=None):
    return Spinner(text=texte or valeurs[0], values=valeurs, size_hint_y=None, height=dp(42))


def _formulaire(titre_txt, widgets, boutons):
    grille = GridLayout(cols=1, spacing=dp(6), size_hint_y=None)
    grille.bind(minimum_height=grille.setter("height"))
    for w in widgets:
        grille.add_widget(w)
    sv = ScrollView()
    sv.add_widget(grille)
    boite = BoxLayout(orientation="vertical", spacing=dp(6), padding=dp(6))
    boite.add_widget(sv)
    pop = Popup(title=titre_txt, content=boite, size_hint=(0.95, 0.9))
    rangee = BoxLayout(spacing=dp(6), size_hint_y=None, height=dp(44))
    for texte, couleur, fn in boutons:
        b = bouton(texte, couleur, 44)
        b.font_size = sp(12)
        b.bind(on_release=lambda x, f=fn: f(pop))
        rangee.add_widget(b)
    boite.add_widget(rangee)
    pop.open()
    return pop


def formulaire_ecriture(sens, apres):
    cats = CATEGORIES_DEPENSES if sens == "D" else CATEGORIES_RECETTES
    date_w = _champ("JJ/MM/AAAA", datetime.now().strftime("%d/%m/%Y"))
    cat = _spinner(cats)
    lib = _champ("Libellé (ex: filtres à huile)")
    tiers = _champ("Fournisseur" if sens == "D" else "Client")
    montant = _champ("Montant (Ar)", input_filter="float")
    mode = _spinner(MODES)
    piece = _champ("N° facture fournisseur (justificatif)" if sens == "D" else "N° de reçu")

    def valider(pop):
        try:
            enregistrer_ecriture(sens, date_w.text, cat.text, lib.text, tiers.text,
                                 prix_nombre(montant.text), mode.text, piece.text)
        except Exception as e:
            afficher_popup("Erreur", str(e))
            return
        pop.dismiss()
        apres()

    _formulaire("NOUVELLE DÉPENSE" if sens == "D" else "AUTRE RECETTE",
                [date_w, cat, lib, tiers, montant, mode, piece],
                [("ENREGISTRER", VERT, valider), ("ANNULER", GRIS, lambda p: p.dismiss())])


def selectionner_facture_paiement(apres):
    """Bouton global toujours visible : choisir une facture impayée pour enregistrer une avance."""
    with db() as c:
        factures = c.execute(
            "SELECT f.id, f.client, f.total, f.date_facture, f.vehicule, f.immatriculation, "
            "COALESCE((SELECT SUM(p.montant) FROM paiements p WHERE p.facture_id=f.id AND p.annule=0),0) AS paye "
            "FROM factures f ORDER BY f.id DESC").fetchall()
    ouvertes = [f for f in factures if float(f["total"] or 0) - float(f["paye"] or 0) > 0.5]
    if not ouvertes:
        afficher_popup("Aucune facture à encaisser", "Aucune facture avec un solde restant n'a été trouvée.")
        return
    contenu = BoxLayout(orientation="vertical", spacing=dp(6), padding=dp(8))
    contenu.add_widget(etiquette("Choisissez la facture sur laquelle enregistrer l'avance :", 13, BLEU_FONCE, True, 38))
    grille = GridLayout(cols=1, spacing=dp(6), size_hint_y=None)
    grille.bind(minimum_height=grille.setter("height"))
    for f in ouvertes:
        reste = max(0, float(f["total"] or 0) - float(f["paye"] or 0))
        texte = "{} — {} | reste {} Ar".format(numero_doc("FAC", f["id"], f["date_facture"]), f["client"] or "Client", prix_affiche(reste))
        b = bouton(texte, VERT, 48)
        b.bind(on_release=lambda _b, fid=f["id"]: (pop.dismiss(), formulaire_paiement(fid, apres)))
        grille.add_widget(b)
    sv = ScrollView(); sv.add_widget(grille); contenu.add_widget(sv)
    pop = Popup(title="Choisir une facture", content=contenu, size_hint=(0.94, 0.86))
    fermer = bouton("FERMER", GRIS, 42); fermer.bind(on_release=lambda *_: pop.dismiss())
    contenu.add_widget(fermer)
    pop.open()


def formulaire_paiement(fid, apres):
    total, paye, hist = infos_paiement(fid)
    reste = total - paye
    infos = [etiquette(f"Total : {prix_affiche(total)}   |   Déjà payé : {prix_affiche(paye)}", 13, BLEU_FONCE, True, 30),
             etiquette(f"Reste à payer : {prix_affiche(reste)}", 13, ROUGE if reste >= 1 else VERT, True, 30)]
    for h in hist:
        ref_txt = f" | Réf. {h['reference']}" if h['reference'] else ""
        infos.append(etiquette(f"   {fr_depuis_iso(h['date_iso'])} : {prix_affiche(h['montant'])} ({h['mode']}){ref_txt}", 11))
    date_w = _champ("JJ/MM/AAAA", datetime.now().strftime("%d/%m/%Y"))
    montant = _champ("Montant encaissé (Ar)", nombre_txt(reste) if reste >= 1 else "", input_filter="float")
    mode = _spinner(MODES)
    reference = _champ("Référence de paiement (facultatif : numéro de transaction / reçu banque)")

    def encaisser(pop):
        try:
            paiement_id = enregistrer_paiement(fid, prix_nombre(montant.text), mode.text, date_w.text, reference.text.strip())
            chemin_recu = generer_pdf_recu_avance(fid, paiement_id)
        except Exception as e:
            afficher_popup("Erreur", str(e))
            return
        pop.dismiss()
        apres()
        popup_actions("Avance enregistrée", "Le paiement est enregistré. Le reçu PDF est prêt à être transmis au client.", [
            ("Ouvrir / partager le reçu PDF", VERT, lambda: ouvrir_ou_partager(chemin_recu)),
            ("Fermer", GRIS, None)])

    def annuler(pop):
        try:
            annuler_dernier_paiement(fid)
        except Exception as e:
            afficher_popup("Erreur", str(e))
            return
        pop.dismiss()
        apres()

    _formulaire("PAIEMENTS DE LA FACTURE", infos + [date_w, montant, mode, reference],
                [("ENCAISSER", VERT, encaisser), ("ANNULER LE DERNIER", ORANGE, annuler),
                 ("FERMER", GRIS, lambda p: p.dismiss())])


def formulaire_inventaire(annee, apres):
    with db() as c:
        actuel = {r["cle"]: r["valeur"] for r in c.execute("SELECT cle, valeur FROM inventaire WHERE annee=?", (annee,))}
    champs = {}
    widgets = [etiquette(f"Inventaire au 31/12/{annee}", 14, BLEU_FONCE, True, 30)]
    for cle, lib in INVENTAIRE_CHAMPS:
        widgets.append(etiquette(lib, 11, GRIS_TEXTE, False, 22))
        champs[cle] = _champ("0", nombre_txt(actuel.get(cle, 0)) if cle in actuel else "", input_filter="float")
        widgets.append(champs[cle])

    def valider(pop):
        with db() as c:
            for cle, w in champs.items():
                c.execute("INSERT OR REPLACE INTO inventaire (annee, cle, valeur) VALUES (?,?,?)",
                          (annee, cle, prix_nombre(w.text)))
        pop.dismiss()
        apres()

    _formulaire("INVENTAIRE DE FIN D'ANNÉE", widgets,
                [("ENREGISTRER", VERT, valider), ("ANNULER", GRIS, lambda p: p.dismiss())])


class JournalScreen(Screen):

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        racine = BoxLayout(orientation="vertical", padding=dp(12), spacing=dp(6))
        racine.add_widget(titre("JOURNAL DE L'ENTREPRISE"))
        haut = BoxLayout(size_hint_y=None, height=dp(42), spacing=dp(6))
        haut.add_widget(etiquette("Exercice :", 13, BLEU_FONCE, True, 42))
        self.annee = Spinner(text=str(datetime.now().year), values=annees_choix())
        self.annee.bind(text=lambda *a: self.rafraichir())
        haut.add_widget(self.annee)
        racine.add_widget(haut)
        self.champ = TextInput(hint_text="Rechercher : libellé, montant, fournisseur, date, recette...",
                               multiline=False, size_hint_y=None, height=dp(42), font_size=sp(13))
        self.champ.bind(text=lambda *a: planifier(self.rafraichir))
        racine.add_widget(self.champ)
        self.resume = etiquette("", 12, VERT, True, 24)
        racine.add_widget(self.resume)
        self.texte = TexteDefilant()
        racine.add_widget(self.texte)

        r1 = BoxLayout(spacing=dp(6), size_hint_y=None, height=dp(44))
        b1 = bouton("+ DÉPENSE", ROUGE, 44)
        b1.bind(on_release=lambda x: formulaire_ecriture("D", self.rafraichir))
        b2 = bouton("+ AUTRE RECETTE", VERT, 44)
        b2.bind(on_release=lambda x: formulaire_ecriture("R", self.rafraichir))
        r1.add_widget(b1)
        r1.add_widget(b2)
        r2 = BoxLayout(spacing=dp(6), size_hint_y=None, height=dp(44))
        b3 = bouton("ANNULER LA DERNIÈRE", ORANGE, 44)
        b3.bind(on_release=lambda x: self.annuler())
        b4 = bouton("EXPORTER", BLEU, 44)
        b4.bind(on_release=lambda x: exporter_dialogue(int(self.annee.text)))
        r2.add_widget(b3)
        r2.add_widget(b4)
        racine.add_widget(r1)
        racine.add_widget(r2)
        racine.add_widget(bouton_retour(self))
        self.add_widget(racine)

    def on_enter(self):
        self.rafraichir()

    @securise
    def rafraichir(self, *args):
        a = analyser_recherche(self.champ.text)
        lignes = filtrer_journal(lignes_journal(int(self.annee.text)), a)
        rec = sum(l["montant"] for l in lignes if l["sens"] == "R" and not l["annule"])
        dep = sum(l["montant"] for l in lignes if l["sens"] == "D" and not l["annule"])
        filtre = bool(a["mots"] or a["debut"] or a["sens"] or a["statuts"])
        self.resume.text = (f"Recettes {prix_affiche(rec)}  |  Dépenses {prix_affiche(dep)}"
                            + ("  (filtré)" if filtre else ""))
        blocs = []
        for l in lignes:
            signe = "+" if l["sens"] == "R" else "-"
            tag = "   [ANNULÉE]" if l["annule"] else ""
            piece = f" | pièce {l['piece']}" if l["piece"] else ""
            blocs.append(f"{l['n']}. {fr_depuis_iso(l['date'])}   {signe}{prix_affiche(l['montant'])}{tag}\n"
                         f"    {l['cat']} - {l['lib']}\n    {l['mode']}{piece}")
        self.texte.set("\n\n".join(blocs) or
                       "Aucune écriture pour cet exercice.\nLes encaissements de factures s'ajoutent "
                       "automatiquement (bouton « Paiements » dans Devis & Factures).")

    def annuler(self):
        popup_actions("Annuler l'écriture", "Annuler la dernière dépense ou recette saisie ?\n"
                      "Elle restera visible, marquée ANNULÉE.", [
                          ("Oui, annuler", ORANGE, self._annuler_ok), ("Non", GRIS, None)])

    @securise
    def _annuler_ok(self):
        annuler_derniere_ecriture()
        self.rafraichir()


class BilanScreen(Screen):

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        racine = BoxLayout(orientation="vertical", padding=dp(12), spacing=dp(6))
        racine.add_widget(titre("BILAN FISCAL"))
        haut = BoxLayout(size_hint_y=None, height=dp(42), spacing=dp(6))
        haut.add_widget(etiquette("Exercice :", 13, BLEU_FONCE, True, 42))
        self.annee = Spinner(text=str(datetime.now().year), values=annees_choix())
        self.annee.bind(text=lambda *a: self.rafraichir())
        haut.add_widget(self.annee)
        racine.add_widget(haut)
        self.texte = TexteDefilant()
        racine.add_widget(self.texte)
        b1 = bouton("INVENTAIRE DE FIN D'ANNÉE", BLEU, 44)
        b1.bind(on_release=lambda x: formulaire_inventaire(int(self.annee.text), self.rafraichir))
        r = BoxLayout(spacing=dp(6), size_hint_y=None, height=dp(44))
        b2 = bouton("EXPORTER PDF + CSV", VERT, 44)
        b2.bind(on_release=lambda x: exporter_dialogue(int(self.annee.text)))
        b3 = bouton("ENVOYER AU COMPTABLE", ORANGE, 44)
        b3.bind(on_release=lambda x: envoyer_au_comptable(int(self.annee.text)))
        r.add_widget(b2)
        r.add_widget(b3)
        racine.add_widget(b1)
        racine.add_widget(r)
        racine.add_widget(bouton_retour(self))
        self.add_widget(racine)

    def on_enter(self):
        self.rafraichir()

    @securise
    def rafraichir(self, *args):
        self.texte.set(texte_synthese(synthese(bilan_annee(int(self.annee.text)))))


# ============================================================
# PARAMÈTRES
# ============================================================

class ParametresScreen(Screen):

    CHAMPS = [("garage_nom", "Nom du garage"), ("garage_adresse", "Adresse"),
              ("garage_nif", "NIF / RCS"), ("garage_contact", "Contacts affichés"),
              ("tva_taux", "TVA % (0 = sans TVA)"), ("smtp_hote", "Serveur SMTP"),
              ("smtp_port", "Port (465 ou 587)"), ("smtp_user", "Votre e-mail"),
              ("smtp_mdp", "Mot de passe d'application"),
              ("email_comptable", "E-mail du comptable"),
              ("ia_cle", "Clé API IA (optionnel)"), ("ia_modele", "Modèle IA"),
              ("is_minimum", "Minimum IS (Ar) selon activité")]

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        racine = BoxLayout(orientation="vertical", padding=dp(15), spacing=dp(8))
        racine.add_widget(titre("PARAMÈTRES"))
        grille = GridLayout(cols=2, spacing=dp(6), size_hint_y=None)
        grille.bind(minimum_height=grille.setter("height"))
        self.saisies = {}
        for cle, lib in self.CHAMPS:
            grille.add_widget(etiquette(lib, 12, BLEU_FONCE, True, 42))
            ti = TextInput(multiline=False, font_size=sp(13), size_hint_y=None, height=dp(42),
                           password=(cle in ("smtp_mdp", "ia_cle")))
            self.saisies[cle] = ti
            grille.add_widget(ti)
        grille.add_widget(etiquette("Envoi auto. des devis corrigés", 12, BLEU_FONCE, True, 42))
        self.auto = Spinner(text="Non", values=("Non", "Oui"), size_hint_y=None, height=dp(42))
        grille.add_widget(self.auto)
        grille.add_widget(etiquette("IA activée (nécessite Internet)", 12, BLEU_FONCE, True, 42))
        self.ia = Spinner(text="Non", values=("Non", "Oui"), size_hint_y=None, height=dp(42))
        grille.add_widget(self.ia)
        grille.add_widget(etiquette("IA autorisée à lire l'historique (données anonymisées)", 12, BLEU_FONCE, True, 42))
        self.ia_historique = Spinner(text="Non", values=("Non", "Oui"), size_hint_y=None, height=dp(42))
        grille.add_widget(self.ia_historique)
        sv = ScrollView()
        sv.add_widget(grille)
        racine.add_widget(sv)
        racine.add_widget(etiquette("Gmail : utilisez un « mot de passe d'application » (validation en 2 étapes).",
                                    11, GRIS, False, 22))
        b1 = bouton("ENREGISTRER", VERT, 45)
        b1.bind(on_release=lambda x: self.enregistrer())
        b2 = bouton("TESTER L'ENVOI D'E-MAIL", ORANGE, 45)
        b2.bind(on_release=lambda x: self.tester())
        b3 = bouton("SAUVEGARDER LA BASE MAINTENANT", BLEU, 45)
        b3.bind(on_release=lambda x: self.sauvegarder())
        b4 = bouton("AUDITER LES PRIX / DÉTECTER LES ERREURS", ORANGE, 45)
        b4.bind(on_release=lambda x: self.auditer_prix())
        racine.add_widget(b1)
        racine.add_widget(b2)
        racine.add_widget(b3)
        racine.add_widget(b4)
        racine.add_widget(bouton_retour(self))
        self.add_widget(racine)

    @securise
    def auditer_prix(self):
        # L'audit est en lecture seule : il ne modifie aucun montant de la base.
        texte = texte_audit_prix_base()
        boite = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(6))
        zone = TexteDefilant(); zone.set(texte); boite.add_widget(zone)
        btn = bouton("FERMER", BLEU_FONCE, 44)
        pop = Popup(title="Audit des prix — lecture seule", content=boite, size_hint=(0.97, 0.9))
        btn.bind(on_release=lambda *_: pop.dismiss()); boite.add_widget(btn); pop.open()

    @securise
    def sauvegarder(self):
        chemin = sauvegarder_base("manuelle")
        if not chemin or not os.path.exists(chemin):
            raise RuntimeError("La sauvegarde n'a pas pu être créée.")
        popup_actions("Sauvegarde créée", f"{os.path.basename(chemin)}\n(15 dernières conservées)", [
            ("Envoyer / partager la copie", ORANGE, lambda: ouvrir_ou_partager(chemin)),
            ("Fermer", GRIS, None)])

    def on_pre_enter(self):
        for cle, ti in self.saisies.items():
            ti.text = param(cle)
        self.auto.text = param("auto_envoi") or "Non"
        self.ia.text = param("ia_active") or "Non"
        self.ia_historique.text = param("ia_historique") or "Non"

    @securise
    def enregistrer(self, silencieux=False):
        for cle, ti in self.saisies.items():
            set_param(cle, ti.text.strip())
        set_param("auto_envoi", self.auto.text)
        set_param("ia_active", self.ia.text)
        set_param("ia_historique", self.ia_historique.text)
        if not silencieux:
            afficher_popup("Paramètres", "Paramètres enregistrés.")

    @securise
    def tester(self):
        self.enregistrer(silencieux=True)
        dest = param("smtp_user")
        if not dest:
            afficher_popup("Test e-mail", "Saisissez d'abord votre adresse e-mail.")
            return
        envoyer_email(dest, "Test CliniqueAutoMada", "L'envoi d'e-mail fonctionne.", None,
                      lambda ok, info: afficher_popup(
                          "Test e-mail",
                          "Envoi réussi : vérifiez votre boîte de réception." if ok else f"Échec : {info}"))


# ============================================================
# IMPORT PDF / WORD : extraction prudente, aperçu et archivage SQL
# ============================================================

def extraire_texte_document(chemin):
    """Extrait le texte d'un PDF textuel ou d'un DOCX. Aucun OCR n'est supposé."""
    ext = os.path.splitext(chemin)[1].lower()
    if ext == ".docx":
        if not zipfile.is_zipfile(chemin):
            raise ValueError("Le fichier Word DOCX est invalide ou endommagé.")
        with zipfile.ZipFile(chemin, "r") as zf:
            try:
                xml = zf.read("word/document.xml")
            except KeyError:
                raise ValueError("Le document Word ne contient pas de texte lisible.")
        root = ET.fromstring(xml)
        ns = {"w": "http://schemas.openxmlformats.org/wordprocessingml/2006/main"}
        lignes = []
        for para in root.findall(".//w:p", ns):
            morceaux = [n.text or "" for n in para.findall(".//w:t", ns)]
            ligne = "".join(morceaux).strip()
            if ligne:
                lignes.append(ligne)
        texte = "\n".join(lignes)
    elif ext == ".pdf":
        texte = ""
        erreurs = []
        try:
            import fitz  # PyMuPDF, si installé
            doc = fitz.open(chemin)
            try:
                texte = "\n".join(page.get_text("text") for page in doc)
            finally:
                doc.close()
        except Exception as e:
            erreurs.append(str(e))
        if not texte.strip():
            try:
                from pypdf import PdfReader
                reader = PdfReader(chemin)
                texte = "\n".join(page.extract_text() or "" for page in reader.pages)
            except Exception as e:
                erreurs.append(str(e))
        if not texte.strip():
            try:
                from PyPDF2 import PdfReader
                reader = PdfReader(chemin)
                texte = "\n".join(page.extract_text() or "" for page in reader.pages)
            except Exception as e:
                erreurs.append(str(e))
        if not texte.strip():
            raise ValueError("Aucun texte PDF exploitable. Le PDF est peut-être scanné (image) ou aucun lecteur PDF compatible n'est installé. "
                             "Pour l'extraction PDF, installez PyMuPDF compatible avec votre Python, ou pypdf.")
    else:
        raise ValueError("Format non pris en charge. Choisissez un PDF ou un Word .docx. Les anciens .doc ne sont pas pris en charge.")
    texte = "\n".join(l.strip() for l in texte.replace("\x00", "").splitlines() if l.strip())
    if not texte:
        raise ValueError("Aucun texte n'a été trouvé dans ce document.")
    return texte


def _empreinte_fichier(chemin):
    """SHA-256 lu par blocs de 1 Mo (V12 chargeait le fichier entier en mémoire)."""
    h = hashlib.sha256()
    with open(chemin, "rb") as f:
        for bloc in iter(lambda: f.read(1 << 20), b""):
            h.update(bloc)
    return h.hexdigest()


class DocumentsScreen(Screen):
    _analyse_en_cours = False

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        racine = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(6))
        racine.add_widget(titre("IMPORT MULTIPLE PDF / WORD VERS LA BASE"))
        racine.add_widget(etiquette(
            "Sélectionnez plusieurs PDF et/ou Word .docx. Utilisez les boutons TOUT SÉLECTIONNER ou VIDER LA SÉLECTION si Ctrl+A ne fonctionne pas. "
            "Cliquez sur EXTRAIRE / APERÇU, vérifiez la liste, puis archivez les documents valides. "
            "Les doublons sont ignorés et les erreurs signalées individuellement. "
            "Aucune fiche client, aucun devis et aucun prix ne sont modifiés automatiquement.",
            12, GRIS_TEXTE, False, 68))
        self.choix = FileChooserListView(path=os.path.expanduser("~"), filters=["*.pdf", "*.docx"],
                                         multiselect=True, size_hint_y=0.38)
        racine.add_widget(self.choix)
        ligne_selection = BoxLayout(size_hint_y=None, height=dp(44), spacing=dp(5))
        b_tout = bouton("TOUT SÉLECTIONNER", BLEU, 42)
        b_aucun = bouton("VIDER LA SÉLECTION", GRIS, 42)
        ligne_selection.add_widget(b_tout); ligne_selection.add_widget(b_aucun)
        racine.add_widget(ligne_selection)
        ligne = BoxLayout(size_hint_y=None, height=dp(44), spacing=dp(5))
        b_analyser = bouton("EXTRAIRE / APERÇU", BLEU, 42)
        b_sauver = bouton("ARCHIVER LA SÉLECTION", VERT, 42)
        ligne.add_widget(b_analyser); ligne.add_widget(b_sauver)
        racine.add_widget(ligne)
        self.apercu = TextInput(text="Sélectionnez un ou plusieurs PDF/DOCX puis cliquez sur EXTRAIRE / APERÇU.",
                                readonly=True, multiline=True, font_size=sp(14), size_hint_y=0.40)
        racine.add_widget(self.apercu)
        b_retour = bouton("RETOUR À L'ACCUEIL", GRIS, 42)
        b_retour.bind(on_release=lambda *_: setattr(self.manager, "current", "accueil"))
        racine.add_widget(b_retour)
        self.documents_prepares = []
        self.add_widget(racine)
        b_tout.bind(on_release=self.selectionner_tout)
        b_aucun.bind(on_release=self.vider_selection)
        b_analyser.bind(on_release=self.analyser)
        b_sauver.bind(on_release=self.archiver)

    @securise
    def selectionner_tout(self, *_):
        """Sélectionne tous les PDF/DOCX visibles dans le dossier courant."""
        fichiers = []
        for chemin in (getattr(self.choix, "files", []) or []):
            try:
                if os.path.isfile(chemin) and os.path.splitext(chemin)[1].lower() in (".pdf", ".docx"):
                    fichiers.append(chemin)
            except Exception:
                continue
        self.choix.selection = fichiers
        self.apercu.text = "Sélection : {} fichier(s). Cliquez sur EXTRAIRE / APERÇU pour continuer.".format(len(fichiers)) if fichiers else "Aucun PDF ou DOCX visible dans ce dossier. Ouvrez le bon dossier puis réessayez."

    @securise
    def vider_selection(self, *_):
        self.choix.selection = []
        self.documents_prepares = []
        self.apercu.text = "Sélection effacée. Choisissez les fichiers à importer."

    @securise
    def analyser(self, *_):
        chemins = list(self.choix.selection or [])
        if not chemins:
            afficher_popup("Aucun fichier", "Sélectionnez un ou plusieurs PDF ou Word .docx, ou cliquez sur TOUT SÉLECTIONNER.")
            return
        if self._analyse_en_cours:
            return
        self._analyse_en_cours = True
        self.documents_prepares = []
        self.apercu.text = "Extraction en cours ({} fichier(s))... patientez.".format(len(chemins))

        def travail():  # thread de fond : l'application ne se fige plus pendant la lecture des PDF
            prepares, journal = [], []
            for chemin in chemins:
                nom = os.path.basename(chemin)
                try:
                    if os.path.splitext(chemin)[1].lower() not in (".pdf", ".docx"):
                        raise ValueError("Format non pris en charge (.pdf ou .docx uniquement).")
                    texte = extraire_texte_document(chemin)
                    prepares.append({"chemin": chemin, "nom": nom, "texte": texte,
                                     "empreinte": _empreinte_fichier(chemin),
                                     "extension": os.path.splitext(chemin)[1].lower()[1:]})
                    journal.append("[PRÊT] {} — {} caractères".format(nom, len(texte)))
                except Exception as exc:
                    journal.append("[ERREUR] {} — {}".format(nom, str(exc)))
            Clock.schedule_once(lambda dt: self._fin_analyse(chemins, prepares, journal))
        threading.Thread(target=travail, daemon=True).start()

    @securise
    def _fin_analyse(self, chemins, prepares, journal):
        self._analyse_en_cours = False
        self.documents_prepares = prepares
        lignes = ["RÉSULTAT DE L'EXTRACTION MULTIPLE", "Sélection : {} fichier(s)".format(len(chemins)), ""]
        lignes.extend(journal)
        lignes.extend(["", "Documents lisibles : {} / {}".format(len(prepares), len(chemins)),
                       "Aperçu limité aux premiers 30 000 caractères par document.", ""])
        for doc in self.documents_prepares:
            lignes.extend(["=" * 55, "FICHIER : {}".format(doc["nom"]), doc["texte"][:30000]])
            if len(doc["texte"]) > 30000:
                lignes.append("[APERÇU TRONQUÉ — le texte complet sera archivé]")
        self.apercu.text = "\n".join(lignes)[:180000]
        if not self.documents_prepares:
            afficher_popup("Aucun document exploitable", "Aucun fichier n'a pu être extrait. Vérifiez les erreurs dans l'aperçu.")

    @securise
    def archiver(self, *_):
        if not self.documents_prepares:
            afficher_popup("Extraction requise", "Sélectionnez plusieurs fichiers, cliquez sur EXTRAIRE / APERÇU et vérifiez les résultats.")
            return
        ajoutes = 0
        doublons = 0
        erreurs = []
        with db() as c:
            for doc in self.documents_prepares:
                try:
                    ancien = c.execute("SELECT id, nom_fichier FROM documents_importes WHERE empreinte_sha256=?",
                                       (doc["empreinte"],)).fetchone()
                    if ancien:
                        doublons += 1
                        erreurs.append("[DOUBLON IGNORÉ] {} (ID {})".format(doc["nom"], ancien["id"]))
                        continue
                    c.execute("""INSERT INTO documents_importes
                        (nom_fichier, chemin_source, type_document, empreinte_sha256, texte_extrait, date_import, nb_caracteres, statut)
                        VALUES (?,?,?,?,?,?,?,?)""",
                        (doc["nom"], doc["chemin"], doc["extension"], doc["empreinte"], doc["texte"],
                         datetime.now().strftime("%Y-%m-%d %H:%M:%S"), len(doc["texte"]), "À vérifier"))
                    ajoutes += 1
                except Exception as exc:
                    erreurs.append("[ÉCHEC] {} — {}".format(doc["nom"], str(exc)))
        resume = ["Documents ajoutés : {}".format(ajoutes), "Doublons ignorés : {}".format(doublons),
                  "Documents préparés : {}".format(len(self.documents_prepares))]
        if erreurs:
            resume.extend(["", "Détails :"] + erreurs[:30])
        resume.extend(["", "Le texte reste archivé séparément. Vérifiez-le avant toute réutilisation."])
        afficher_popup("Import multiple terminé", "\n".join(resume))
        self.documents_prepares = []



# ============================================================
# DIAGNOSTIC PRÉACHAT — RAPPORT PDF
# ============================================================

class DiagnosticPreachatScreen(Screen):
    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        racine = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(6))
        racine.add_widget(titre("DIAGNOSTIC PRÉACHAT — FIMPIBAMA"))
        racine.add_widget(etiquette("Renseignez les informations et observations. Le rapport PDF sera enregistré dans PDF_Export.", 12, GRIS_TEXTE, False, 36))
        scroll = ScrollView()
        contenu = GridLayout(cols=2, spacing=dp(6), padding=dp(4), size_hint_y=None)
        contenu.bind(minimum_height=contenu.setter("height"))
        self.champs = {}
        def champ(libelle, valeur="", multiline=False):
            contenu.add_widget(Label(text=libelle, color=GRIS_TEXTE, size_hint_y=None, height=dp(42), halign="left", valign="middle"))
            inp = TextInput(text=valeur, multiline=multiline, size_hint_y=None, height=dp(90) if multiline else dp(42),
                            font_size=sp(14), hint_text=libelle)
            self.champs[libelle] = inp
            contenu.add_widget(inp)
        champ("Client", "FIMPIBAMA")
        champ("Téléphone client (WhatsApp)")
        champ("Date", datetime.now().strftime("%d/%m/%Y"))
        champ("Marque / modèle")
        champ("Immatriculation")
        champ("VIN / numéro de châssis")
        champ("Kilométrage")
        champ("Motorisation / boîte")
        champ("Diagnostic électronique", "Codes défauts, calculateurs interrogés, résultats…", True)
        champ("Moteur / turbo / refroidissement", "Fuites, bruits, fumée, niveaux, fonctionnement…", True)
        champ("Boîte / transmission", "Passage des rapports, bruits, fuites, essai…", True)
        champ("Freinage / suspension / direction", "État et anomalies constatées…", True)
        champ("Carrosserie / châssis", "Traces de choc, réparations, corrosion, alignements…", True)
        champ("Essai routier", "Conditions et résultats, si effectué…", True)
        champ("Réparations à prévoir", "Détailler les travaux recommandés et les priorités…", True)
        champ("Estimation des réparations (Ar)")
        champ("Conclusion professionnelle", "Favorable / favorable sous réserves / déconseillé — préciser les limites du contrôle.", True)
        scroll.add_widget(contenu)
        racine.add_widget(scroll)
        self.dernier_pdf = ""
        ligne = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(6))
        b_pdf = bouton("GÉNÉRER PDF", VERT, 44)
        b_voir = bouton("VOIR LE PDF", BLEU, 44)
        b_whatsapp = bouton("ENVOYER WHATSAPP", ORANGE, 44)
        ligne.add_widget(b_pdf); ligne.add_widget(b_voir); ligne.add_widget(b_whatsapp)
        racine.add_widget(ligne)
        ligne2 = BoxLayout(size_hint_y=None, height=dp(42), spacing=dp(6))
        b_retour = bouton("RETOUR", GRIS, 40)
        ligne2.add_widget(b_retour)
        racine.add_widget(ligne2)
        self.status = etiquette("Générez d'abord le rapport PDF, puis affichez-le ou partagez-le.", 11, GRIS_TEXTE, False, 34)
        racine.add_widget(self.status)
        b_pdf.bind(on_release=self.generer)
        b_voir.bind(on_release=self.voir_pdf)
        b_whatsapp.bind(on_release=self.envoyer_whatsapp)
        b_retour.bind(on_release=lambda *_: setattr(self.manager, "current", "accueil"))
        self.add_widget(racine)

    @securise
    def generer(self, *_):
        if not HAS_REPORTLAB:
            afficher_popup("PDF indisponible", "ReportLab n'est pas installé. Installez reportlab puis relancez l'application.")
            return
        d = {k: v.text.strip() for k, v in self.champs.items()}
        if not d.get("Marque / modèle") and not d.get("Immatriculation"):
            afficher_popup("Informations manquantes", "Saisissez au moins la marque/modèle ou l'immatriculation du véhicule.")
            return
        ident = nom_fichier_sur(d.get("Immatriculation") or d.get("Marque / modèle") or "vehicule")
        numero = datetime.now().strftime("DPA-%Y%m%d-%H%M%S")
        chemin = os.path.join(DOSSIER_PDF, "{}_{}.pdf".format(numero, ident))
        c = canvas.Canvas(chemin, pagesize=A4)
        largeur, hauteur = A4
        x, y = 42, hauteur - 48
        def page_suivante():
            nonlocal y
            c.showPage(); y = hauteur - 48
            c.setFont("Helvetica-Bold", 12); c.drawString(x, y, "DIAGNOSTIC PRÉACHAT — {}".format(numero)); y -= 24
        c.setTitle("Diagnostic préachat {} - FIMPIBAMA".format(ident))
        c.setFont("Helvetica-Bold", 16); c.setFillColorRGB(0.08, 0.22, 0.42)
        c.drawString(x, y, str(param("garage_nom") or "CLINIQUE AUTO MADA")[:70]); y -= 20
        c.setFillColorRGB(0,0,0); c.setFont("Helvetica", 9)
        for cle in ("garage_adresse", "garage_contact", "garage_nif"):
            val = param(cle)
            if val: c.drawString(x, y, str(val)[:110]); y -= 13
        y -= 8; c.setFont("Helvetica-Bold", 14); c.drawString(x, y, "RAPPORT DE DIAGNOSTIC PRÉACHAT"); y -= 22
        c.setFont("Helvetica", 10); c.drawString(x, y, "Référence : {}    Date : {}".format(numero, d.get("Date", ""))); y -= 18
        for cle in ("Client", "Marque / modèle", "Immatriculation", "VIN / numéro de châssis", "Kilométrage", "Motorisation / boîte"):
            val = d.get(cle, "") or "Non renseigné"
            c.setFont("Helvetica-Bold", 9); c.drawString(x, y, cle + " :")
            c.setFont("Helvetica", 9); c.drawString(x + 145, y, val[:85]); y -= 15
        y -= 5
        sections = ["Diagnostic électronique", "Moteur / turbo / refroidissement", "Boîte / transmission",
                    "Freinage / suspension / direction", "Carrosserie / châssis", "Essai routier",
                    "Réparations à prévoir", "Estimation des réparations (Ar)", "Conclusion professionnelle"]
        for cle in sections:
            if y < 95: page_suivante()
            c.setFont("Helvetica-Bold", 10); c.setFillColorRGB(0.08, 0.22, 0.42); c.drawString(x, y, cle); y -= 14
            c.setFillColorRGB(0,0,0); c.setFont("Helvetica", 9)
            texte = d.get(cle, "") or "Aucune observation renseignée."
            for ligne_txt in simpleSplit(texte, "Helvetica", 9, largeur - 2*x):
                if y < 55: page_suivante(); c.setFont("Helvetica", 9)
                c.drawString(x + 4, y, ligne_txt); y -= 12
            y -= 7
        if y < 65: page_suivante()
        c.setFont("Helvetica-Oblique", 8)
        c.drawString(x, 36, "Rapport établi selon les contrôles réalisés et les éléments accessibles le jour de l'inspection.")
        c.save()
        self.dernier_pdf = chemin
        self.status.text = "PDF créé : " + chemin
        afficher_popup("Rapport PDF généré", "Le rapport de diagnostic préachat a été enregistré :\n\n" + chemin + "\n\nVous pouvez maintenant cliquer sur VOIR LE PDF ou ENVOYER WHATSAPP.")

    @securise
    def voir_pdf(self, *_):
        chemin = self.dernier_pdf
        if not chemin or not os.path.isfile(chemin):
            afficher_popup("PDF indisponible", "Générez d'abord le rapport PDF.")
            return
        ouvrir_ou_partager(chemin)

    @securise
    def envoyer_whatsapp(self, *_):
        chemin = self.dernier_pdf
        if not chemin or not os.path.isfile(chemin):
            afficher_popup("PDF indisponible", "Générez d'abord le rapport PDF avant de l'envoyer.")
            return
        d = {k: v.text.strip() for k, v in self.champs.items()}
        telephone = d.get("Téléphone client (WhatsApp)", "")
        client = d.get("Client", "FIMPIBAMA") or "FIMPIBAMA"
        vehicule = d.get("Marque / modèle", "") or d.get("Immatriculation", "") or "véhicule inspecté"
        message = ("Bonjour {},\n\nVeuillez trouver le rapport de diagnostic préachat de {} réalisé par Clinique Auto Mada.\n"
                   "Référence : {}\nLe rapport PDF est joint à cet envoi.\n\nCordialement,\nClinique Auto Mada").format(
                       client, vehicule, os.path.basename(chemin).replace(".pdf", ""))
        partager_pdf_whatsapp(telephone, message, chemin, "rapport de diagnostic préachat")


# ============================================================
# ACCUEIL (avec tableau de bord)
# ============================================================

class AccueilScreen(Screen):

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        layout = BoxLayout(orientation="vertical", padding=dp(20), spacing=dp(10))
        layout.add_widget(Label(text="CLINIQUE AUTO MADA", font_size=sp(24), bold=True,
                                color=BLEU_FONCE, size_hint_y=None, height=dp(50)))
        self.stats = Label(text="", font_size=sp(13), color=GRIS_TEXTE, halign="center",
                           size_hint_y=None, height=dp(75))
        layout.add_widget(self.stats)

        scroll = ScrollView()
        menu = GridLayout(cols=2, spacing=dp(10), padding=dp(5), size_hint_y=None)
        menu.bind(minimum_height=menu.setter("height"))
        for texte, ecran in [("NOUVEAU DEVIS", "devis"), ("DEVIS & FACTURES", "factures"),
                             ("CLIENTS", "clients"), ("VÉHICULES", "vehicules"),
                             ("RECHERCHE", "recherche"), ("PRIX HABITUELS", "historique"),
                             ("JOURNAL", "journal"), ("BILAN FISCAL", "bilan"),
                             ("PDF / WORD → BASE", "documents"), ("DIAGNOSTIC PRÉACHAT", "diagnostic_preachat"), ("PARAMÈTRES", "parametres")]:
            b = bouton(texte, BLEU, 55)
            b.bind(on_release=lambda x, e=ecran: self.aller(e))
            menu.add_widget(b)
        quitter = bouton("QUITTER", ROUGE, 55)
        quitter.bind(on_release=lambda x: App.get_running_app().stop())
        menu.add_widget(quitter)
        scroll.add_widget(menu)
        layout.add_widget(scroll)
        self.add_widget(layout)

    def aller(self, ecran):
        if ecran == "devis":
            self.manager.get_screen("devis").reinitialiser()
        self.manager.current = ecran

    def on_enter(self):
        try:
            ca, impaye, nb_imp, attente = stats()
            self.stats.text = (f"Encaissé ce mois-ci : {prix_affiche(ca)}\n"
                               f"Factures impayées : {nb_imp} ({prix_affiche(impaye)})\n"
                               f"Devis en attente : {attente}")
        except Exception as e:
            self.stats.text = f"Statistiques indisponibles : {e}"


# ============================================================
# APPLICATION
# ============================================================

class CliniqueAutoMadaApp(App):
    title = "Clinique Auto Mada V13"

    def build(self):
        init_chemins(self)
        init_database()
        sm = ScreenManager()
        sm.add_widget(AccueilScreen(name="accueil"))
        sm.add_widget(DevisScreen(name="devis"))
        sm.add_widget(FacturesScreen(name="factures"))
        sm.add_widget(ResultatsScreen("CLIENTS", {"client"}, name="clients"))
        sm.add_widget(ResultatsScreen("VÉHICULES", {"vehicule"}, name="vehicules"))
        sm.add_widget(ListeScreen("PRIX HABITUELS", donnees_historique, True, name="historique"))
        sm.add_widget(ResultatsScreen("RECHERCHE", {"client", "vehicule", "devis", "facture"}, name="recherche"))
        sm.add_widget(JournalScreen(name="journal"))
        sm.add_widget(BilanScreen(name="bilan"))
        sm.add_widget(DocumentsScreen(name="documents"))
        sm.add_widget(DiagnosticPreachatScreen(name="diagnostic_preachat"))
        sm.add_widget(ParametresScreen(name="parametres"))
        Window.bind(on_keyboard=self.touche)
        # Sauvegarde du jour + contrôle d'intégrité : lancés APRÈS l'affichage de l'accueil,
        # dans un thread (V12 les exécutait avant d'ouvrir la fenêtre).
        Clock.schedule_once(lambda dt: threading.Thread(target=self._controles_differes, daemon=True).start(), 1)
        return sm

    def _controles_differes(self):
        try:
            sauvegarde_du_jour()
            sain = verifier_integrite()
        except sqlite3.DatabaseError as e:
            sain = "locked" in str(e).lower()      # base verrouillée = pas une corruption
        except Exception:
            sain = True
        if not sain:
            Clock.schedule_once(lambda dt: afficher_popup(
                "Base endommagée", "La base présente une anomalie.\nRestaurez une copie du dossier Sauvegardes."), 0)
        try:                                        # met à jour les statistiques du planificateur SQLite
            with db() as c:
                c.execute("PRAGMA optimize")
        except Exception:
            pass

    def touche(self, window, key, *args):
        """Bouton retour d'Android : revient à l'accueil au lieu de fermer l'application."""
        if key == 27 and self.root.current != "accueil":
            self.root.current = "accueil"
            return True
        return False


if __name__ == "__main__":
    CliniqueAutoMadaApp().run()