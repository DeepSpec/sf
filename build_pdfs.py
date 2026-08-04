#!/usr/bin/env python3
import os
import sys
import glob
import subprocess
import shutil

VOLS = {
    "lf": "LF",
    "plf": "PLF",
    "vfa": "VFA",
    "qc": "QuickChick",
    "vc": "VC",
    "slf": "SLF",
    "secf": "SECF"
}

def build_pdf_for_volume(vol, prefix):
    vol_dir = f"{vol}-current"
    if not os.path.exists(vol_dir):
        print(f"Directory {vol_dir} does not exist. Skipping.")
        return False

    print(f"\n=========================================")
    print(f"   Building PDF for {vol.upper()} ({prefix})")
    print(f"=========================================\n")

    # Apply volume patch if available
    patch_file = os.path.abspath(os.path.join("patches", f"{vol}.patch"))
    if os.path.exists(patch_file):
        print(f"Applying patch {patch_file} to {vol_dir}...")
        subprocess.run(["patch", "-N", "-p1", "-i", patch_file], cwd=vol_dir, check=False)

    subprocess.run(["make", "-C", vol_dir, "clean"], check=False)
    subprocess.run(["make", "-C", vol_dir, "all"], check=False)

    makefile_path = os.path.join(vol_dir, "Makefile")
    vfiles = []
    if os.path.exists(makefile_path):
        with open(makefile_path, 'r', encoding='utf-8') as f:
            for line in f:
                if line.startswith("ALLVFILES"):
                    parts = line.split(":=")[1].split()
                    vfiles = [p for p in parts if p.endswith(".v")]
                    break

    if not vfiles:
        vfiles = [os.path.basename(p) for p in glob.glob(os.path.join(vol_dir, "*.v"))]

    print(f"Files for {vol}: {len(vfiles)} files found.")

    coqdoc_cmd = ["coqdoc", "-latex", "-toc", "-interpolate", "-utf8", "-Q", ".", prefix] + vfiles
    subprocess.run(coqdoc_cmd, cwd=vol_dir, check=False)

    all_tex_path = os.path.join(vol_dir, "all.tex")
    with open(all_tex_path, 'w', encoding='utf-8') as f:
        f.write("\\documentclass[12pt]{report}\n")
        f.write("\\usepackage[utf8x]{inputenc}\n")
        f.write("\\usepackage[T1]{fontenc}\n")
        f.write("\\usepackage{fullpage}\n")
        f.write("\\usepackage[color]{coqdoc}\n")
        f.write("\\usepackage{amsmath,amssymb,latexsym}\n")
        f.write("\\usepackage{url}\n")
        f.write("\\usepackage{pmboxdraw}\n")
        f.write("\\usepackage{newunicodechar}\n")
        f.write("\\usepackage{xcolor}\n")
        f.write("\\usepackage{hyperref}\n")

        # Color definitions matching Software Foundations CSS palette
        f.write("\\definecolor{sfblue}{HTML}{416DFF}\n")
        f.write("\\definecolor{sfkw}{HTML}{697F2F}\n")
        f.write("\\definecolor{sfdef}{HTML}{006600}\n")
        f.write("\\definecolor{sfind}{HTML}{034764}\n")
        f.write("\\definecolor{sfvar}{HTML}{660066}\n")
        f.write("\\definecolor{sfconstr}{HTML}{697F2F}\n")
        f.write("\\definecolor{sfcomment}{HTML}{808080}\n")

        f.write("\\hypersetup{\n")
        f.write("    colorlinks=true,\n")
        f.write("    linkcolor=sfblue,\n")
        f.write("    citecolor=sfblue,\n")
        f.write("    urlcolor=sfblue\n")
        f.write("}\n")

        # Custom macro overrides for coqdoc syntax highlighting
        f.write("\\renewcommand{\\coqdockw}[1]{{\\color{sfkw}{\\textbf{\\texttt{#1}}}}}\n")
        f.write("\\renewcommand{\\coqdocvar}[1]{{\\color{sfvar}{\\textit{#1}}}}\n")
        f.write("\\renewcommand{\\coqdoccst}[1]{{\\color{sfdef}{\\textrm{#1}}}}\n")
        f.write("\\renewcommand{\\coqdocind}[1]{{\\color{sfind}{\\textsf{\\textbf{#1}}}}}\n")
        f.write("\\renewcommand{\\coqdocconstr}[1]{{\\color{sfconstr}{\\textsf{#1}}}}\n")
        f.write("\\renewcommand{\\coqdocmod}[1]{{\\color{sfdef}{\\textsc{\\textsf{#1}}}}}\n")
        f.write("\\renewcommand{\\coqdocax}[1]{{\\color{sfvar}{\\textsl{\\textrm{#1}}}}}\n")
        f.write("\\renewcommand{\\coqdoctac}[1]{{\\color{sfkw}{\\texttt{#1}}}}\n")

        f.write("\\begin{document}\n")
        f.write(f"\\title{{\\Huge \\textbf{{Software Foundations: {vol.upper()}}}}}\n")
        f.write("\\maketitle\n")
        f.write("\\tableofcontents\n")

        for vf in vfiles:
            mod_name = os.path.splitext(vf)[0]
            tex_file = f"{prefix}.{mod_name}.tex"
            tex_path = os.path.join(vol_dir, tex_file)
            if not os.path.exists(tex_path):
                tex_file = f"{mod_name}.tex"
                tex_path = os.path.join(vol_dir, tex_file)

            if os.path.exists(tex_path):
                cleaned_lines = []
                with open(tex_path, 'r', encoding='utf-8', errors='ignore') as tf:
                    in_doc = False
                    for l in tf:
                        if l.startswith('\\begin{document}'):
                            in_doc = True
                            continue
                        if l.startswith('\\end{document}'):
                            in_doc = False
                            continue
                        if in_doc:
                            cleaned_lines.append(l)

                cleaned_file = f"clean_{tex_file}"
                with open(os.path.join(vol_dir, cleaned_file), 'w', encoding='utf-8') as cf:
                    cf.writelines(cleaned_lines)

                f.write(f"\\input{{{cleaned_file}}}\n")

        f.write("\\end{document}\n")

    # Pass 1: Generate .aux and table of contents
    subprocess.run(["pdflatex", "-interaction=nonstopmode", "all.tex"], cwd=vol_dir, check=False)
    # Pass 2: Resolve page numbers and references into final PDF
    subprocess.run(["pdflatex", "-interaction=nonstopmode", "all.tex"], cwd=vol_dir, check=False)

    generated_pdf = os.path.join(vol_dir, "all.pdf")
    os.makedirs("doc/pdf", exist_ok=True)
    target_pdf = f"doc/pdf/{vol}.pdf"

    success = False
    if os.path.exists(generated_pdf):
        shutil.move(generated_pdf, target_pdf)
        print(f"SUCCESS: Generated {target_pdf}")
        success = True
    else:
        print(f"ERROR: Failed to generate {target_pdf}")
        success = False

    # Clean up intermediate TeX artifacts
    for ext in ["all.tex", "all.aux", "all.log", "all.toc", "all.out", "all.fls", "all.fdb_latexmk"]:
        p = os.path.join(vol_dir, ext)
        if os.path.exists(p):
            os.remove(p)

    for clean_f in glob.glob(os.path.join(vol_dir, "clean_*.tex")):
        if os.path.exists(clean_f):
            os.remove(clean_f)

    return success

def main():
    args = sys.argv[1:]
    target_vols = VOLS.keys()
    if args:
        target_vols = [a.lower() for a in args if a.lower() in VOLS]

    for vol in target_vols:
        build_pdf_for_volume(vol, VOLS[vol])

if __name__ == "__main__":
    main()
