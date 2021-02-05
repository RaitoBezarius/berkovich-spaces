#!/usr/bin/env bash
pandoc main.md --biblatex --lua-filter=filters/scholarly-metadata.lua --lua-filter=filters/author-info-blocks.lua --template=template.latex -so main.tex
latexmk -pdf main.tex
latexmk -c
