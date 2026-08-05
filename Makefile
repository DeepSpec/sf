all: lf plf vfa qc vc slf secf

.PHONY: all clean serve coqdoc-pdf html-pdf lf plf vfa qc vc slf secf

clean:
	for dir in *-current; do $(MAKE) -C $$dir clean || true; done
	rm -rf doc/pdf src

serve:
	python3 -m http.server 8000

coqdoc-pdf:
	python3 build_pdfs.py

html-pdf:
	python3 build_html_pdfs.py

lf:
	python3 build_pdfs.py lf
	python3 build_html_pdfs.py lf

plf:
	python3 build_pdfs.py plf
	python3 build_html_pdfs.py plf

vfa:
	python3 build_pdfs.py vfa
	python3 build_html_pdfs.py vfa

qc:
	python3 build_pdfs.py qc
	python3 build_html_pdfs.py qc

vc:
	python3 build_pdfs.py vc
	python3 build_html_pdfs.py vc

slf:
	python3 build_pdfs.py slf
	python3 build_html_pdfs.py slf

secf:
	python3 build_pdfs.py secf
	python3 build_html_pdfs.py secf
