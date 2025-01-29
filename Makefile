default:
	stack build

testcoverage:
	stack clean
	stack test --coverage
	xdg-open .stack-work/install/*/*/*/hpc/combined/all/hpc_index.html

clean:
	stack clean
	find src/ -iname *.hi -type f -print | xargs /bin/rm -f
	find src/ -iname *.o -type f -print | xargs /bin/rm -f

bench/muddychildren.pdf: Makefile bench/muddychildren.hs bench/muddychildren.tex
	stack bench :bench-muddychildren --benchmark-arguments "--csv bench/muddychildren-results.csv"
	cd bench && latexmk -pdf -quiet -interaction=nonstopmode muddychildren

todo:
	@bash -c 'grep -nr "TODO" {src,exec,test,bench}'
	@bash -c 'grep -nr "FIXME" {src,exec,test,bench}'

ACEVERSION = 1.5.0

static/ace.js:
	wget -c "https://github.com/ajaxorg/ace-builds/archive/v$(ACEVERSION).tar.gz" -O static/ace.tgz
	tar xz -C static -f static/ace.tgz ace-builds-$(ACEVERSION)/src-min-noconflict/ace.js
	mv static/ace-builds-$(ACEVERSION)/src-min-noconflict/ace.js static/ace.js
	rm -rf static/ace-builds-$(ACEVERSION)
	rm static/ace.tgz

.PHONY: default testcoverage clean release todo
