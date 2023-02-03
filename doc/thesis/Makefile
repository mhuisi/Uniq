BUILD=build
BASE=thesis
DEPS=$(shell find . -name "*.tex") $(shell find . -name "*.sty")

default: $(BASE).pdf

$(BUILD)/$(BASE).pdf: $(BASE).tex $(DEPS)
	mkdir -p $(BUILD)
	TEXINPUTS=$(TEXINPUTS):style latexmk -f -pdf -jobname=build/$(BASE) -interaction=nonstopmode $<

$(BASE).pdf: $(BUILD)/$(BASE).pdf
	mv $< $@ # atomic update
	cp $@ $<

.PHONY: show watch clean

show: $(BASE).pdf
	xdg-open $< || open $<

watch: $(BASE).pdf
	inotifywait -q -m -e close_write,move_self --exclude 'build/|$(subst .,\.,$<)' * | while read -r line; do $(MAKE); done

clean:
	rm -rf build
