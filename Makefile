all:
	happy -gca ParkCP.y
	alex -g LexkCP.x
	latex DockCP.tex; dvips DockCP.dvi -o DockCP.ps
	ghc --make Interpreter.hs -o Interpreter
clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f DockCP.ps
distclean: clean
	-rm -f DockCP.* LexkCP.* ParkCP.* LayoutkCP.* SkelkCP.* PrintkCP.* Interpreter.* AbskCP.* Interpreter ErrM.* SharedString.* kCP.dtd XMLkCP.* Makefile*

