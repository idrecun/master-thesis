#!/bin/bash
latexmk -f -pdf -interaction=nonstopmode master >/dev/null 2>/dev/null
xdg-open master.pdf >/dev/null 2>/dev/null &
