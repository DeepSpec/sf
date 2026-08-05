#!/usr/bin/env python3
import os
import sys
import re
import subprocess
import shutil
from concurrent.futures import ThreadPoolExecutor

VOLUMES = [
    ("lf", "Logical Foundations"),
    ("plf", "Programming Language Foundations"),
    ("vfa", "Verified Functional Algorithms"),
    ("qc", "QuickChick: Property-Based Testing in Coq"),
    ("vc", "Verifiable C"),
    ("slf", "Separation Logic Foundations"),
    ("secf", "Security Foundations")
]

def find_chrome_binary():
    candidates = [
        "google-chrome",
        "google-chrome-stable",
        "chromium",
        "brave",
        "chrome"
    ]
    for c in candidates:
        path = shutil.which(c)
        if path:
            return path
    fallback = "/run/current-system/sw/bin/google-chrome"
    if os.path.exists(fallback):
        return fallback
    raise RuntimeError("No Chrome/Chromium binary found in PATH.")

def find_pdfunite_binary():
    path = shutil.which("pdfunite")
    if path:
        return path
    fallback = "/run/current-system/sw/bin/pdfunite"
    if os.path.exists(fallback):
        return fallback
    raise RuntimeError("pdfunite binary not found in PATH.")

def extract_chapter_order(vol_dir):
    toc_path = os.path.join(vol_dir, "toc.html")
    if not os.path.exists(toc_path):
        return sorted([f for f in os.listdir(vol_dir) if f.endswith(".html") and f != "index.html"])

    with open(toc_path, 'r', encoding='utf-8', errors='ignore') as f:
        html_content = f.read()

    main_chapters = []
    links = re.findall(r'href=["\']([^"\']+\.html)(?:#[^"\']*)?["\']', html_content)
    for link in links:
        fn = os.path.basename(link)
        if fn in ["toc.html", "index.html", "coqindex.html", "deps.html"]:
            continue
        if fn not in main_chapters and os.path.exists(os.path.join(vol_dir, fn)):
            main_chapters.append(fn)

    ordered = []
    if os.path.exists(os.path.join(vol_dir, "toc.html")):
        ordered.append("toc.html")

    ordered.extend(main_chapters)

    for aux in ["coqindex.html", "deps.html"]:
        if os.path.exists(os.path.join(vol_dir, aux)) and aux not in ordered:
            ordered.append(aux)

    return ordered

def convert_html_to_pdf(chrome_bin, html_path, out_pdf_path):
    abs_html = os.path.abspath(html_path)
    file_url = f"file://{abs_html}"
    cmd = [
        chrome_bin,
        "--headless",
        "--disable-gpu",
        "--no-sandbox",
        "--no-pdf-header-footer",
        f"--print-to-pdf={out_pdf_path}",
        file_url
    ]
    subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)

def build_pdf_for_vol(vol_code, vol_title, chrome_bin, pdfunite_bin, tmp_dir):
    vol_dir = f"{vol_code}-current"
    if not os.path.exists(vol_dir):
        print(f"Skipping {vol_code}: directory {vol_dir} not found.")
        return None

    print(f"\n=========================================")
    print(f"  Building HTML -> PDF Book for {vol_code.upper()} ({vol_title})")
    print(f"=========================================")

    chapters = extract_chapter_order(vol_dir)
    print(f"Found {len(chapters)} chapter HTML files for {vol_code.upper()}.")

    vol_tmp_dir = os.path.join(tmp_dir, vol_code)
    if os.path.exists(vol_tmp_dir):
        shutil.rmtree(vol_tmp_dir)
    os.makedirs(vol_tmp_dir, exist_ok=True)

    tasks = []
    chapter_pdfs = []
    for idx, ch in enumerate(chapters):
        html_path = os.path.join(vol_dir, ch)
        out_pdf = os.path.join(vol_tmp_dir, f"{idx:03d}_{ch.replace('.html', '.pdf')}")
        chapter_pdfs.append(out_pdf)
        tasks.append((html_path, out_pdf))

    with ThreadPoolExecutor(max_workers=8) as executor:
        futures = [executor.submit(convert_html_to_pdf, chrome_bin, hp, op) for hp, op in tasks]
        for f in futures:
            f.result()

    os.makedirs("doc/pdf", exist_ok=True)
    vol_pdf_path = f"doc/pdf/{vol_code}_html.pdf"

    unite_cmd = [pdfunite_bin] + chapter_pdfs + [vol_pdf_path]
    subprocess.run(unite_cmd, check=True)

    shutil.rmtree(vol_tmp_dir, ignore_errors=True)

    print(f"SUCCESS: Generated 1 book PDF for {vol_code.upper()}: {vol_pdf_path}")
    return vol_pdf_path

def main():
    chrome_bin = find_chrome_binary()
    pdfunite_bin = find_pdfunite_binary()

    base_tmp_dir = "/tmp/sf_html_pdf_build"
    os.makedirs(base_tmp_dir, exist_ok=True)

    args = sys.argv[1:]
    target_vols = [v[0] for v in VOLUMES]
    if args:
        target_vols = [a.lower() for a in args if any(v[0] == a.lower() for v in VOLUMES)]

    for vol_code, vol_title in VOLUMES:
        if vol_code in target_vols:
            build_pdf_for_vol(vol_code, vol_title, chrome_bin, pdfunite_bin, base_tmp_dir)

if __name__ == "__main__":
    main()
