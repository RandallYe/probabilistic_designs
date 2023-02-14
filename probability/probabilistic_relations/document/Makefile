#
# Makefile for compiling pdf file from tex file
# 
OS := $(shell uname -s)
PWD := $(shell pwd)
BNAME := root
PDF := $(BNAME).pdf #$(patsubst %.tex,%.pdf, $(wildcard *.tex))

ifeq ($(OS), Darwin)
OS := OSX 
TEXS := $(foreach f, $(wildcard *.tex), $(PWD)/$(f))
#EDIT := /Applications/MacVim.app/Contents/MacOS/MacVim --servername vimsvr -g -f -p --remote-silent $(TEXS)
### open multi tabs and each tab for each file
EDIT := mvim -p --servername vimsvr -g -f $(TEXS)
### open one tab for all files
#EDIT := mvim --servername vimsvr -g -f $(TEXS)
OPEN := open
endif

ifeq ($(OS), Linux)
	OS := Linux 
endif

ifneq (,$(findstring CYGWIN_NT, $(OS)))
# CYGWIN_NT
# Convert cygwin path to Windows path, and replace one \ with two \\ 
WIN_PWD := $(shell cygpath -w ${PWD} | sed 's/\\/\\\\/g')
TEXS := $(foreach f, $(wildcard *.tex), $(WIN_PWD)\\$(f))
PYTHON27 := C:\\python27
GVIM := d:\\randall\\programs\\gvim73\\vim73\\gvim.exe
OS := CYGWIN_NT
OPEN := cygstart.exe
endif

ifeq (,$(OS))
$(error OS can not be determined)
endif

.PHONY: all show clean edit open 
all: clean $(PDF) 

show:
	@echo $(OS)

# clean 
clean: 
	-@rm -f *.aux *.lof *.log *.lot *.out *.toc *.bbl *.blg *.pdf *.nav *.snm 

edit:
ifneq (,$(findstring CYGWIN_NT, $(OS)))
	/cygdrive/c/Windows/System32/cmd.exe /C start /D $(PYTHON27) $(GVIM) -g -f -p --servername vimsvr --remote-silent $(TEXS)
endif
ifeq ($(OS), OSX)
	@echo "Edit $(EDIT) $(TEXS) &"
	@$(EDIT) &
endif
	@echo "Edit $(EDIT) $(TEXS) &"
	@$(EDIT) &

open: $(PDF)
	@$(OPEN) $< &

%.pdf: %.tex *.tex
	@echo "Compiling pdf file $(basename $<).pdf from $<"
	pdflatex $< # if the exit code of this command is not 0, then exit
	-bibtex $(basename $<)  # even this command fails, continue
	-bibtex $(basename $<)
	-bibtex $(basename $<)
	-pdflatex $<
	-pdflatex $<
	-pdflatex $<

fast: *.tex 
	@echo "Compiling pdf file $(BNAME).pdf from $(BNAME).tex"
	pdflatex $(BNAME).tex
	@$(OPEN) $(BNAME).pdf &

pic: pic/*.png

pic/%.png: pic/%.gv
	@echo "dot -Tpng $< -o $@"
	dot -Tpng $< -o "$(basename $<).png"

build_doc: build 

build:
	isabelle2017 build -d /Users/rye/Workspace_VeTSS/VeTSS.working/isabelle-utp/contract -b Simulink
	make -C ../output/document update

update:
	-bibtex root  # even this command fails, continue
	-bibtex root  # even this command fails, continue
	-bibtex root  # even this command fails, continue
	-pdflatex root 
	-pdflatex root 
	-pdflatex root 
	
