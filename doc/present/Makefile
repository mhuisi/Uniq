BUILD=build
BASE=present
DEPS=$(wildcard *.tex) $(wildcard *.sty)

default: $(BASE).pdf

$(BUILD)/$(BASE).pdf: $(BASE).tex $(DEPS)
	mkdir -p $(BUILD)
	TEXINPUTS=style:$(TEXINPUTS) latexmk -f -pdf -outdir=build -interaction=nonstopmode $<

$(BASE).pdf: $(BUILD)/$(BASE).pdf
	mv $< $@ # atomic update
	cp $@ $<

.PHONY: show watch clean

show: $(BASE).pdf
	gnome-open $< || open $<

watch: $(BASE).pdf
	inotifywait -q -m -e close_write,move_self --exclude 'build/|$(subst .,\.,$<)' * | while read -r line; do $(MAKE); done

clean:
	rm -rf build
