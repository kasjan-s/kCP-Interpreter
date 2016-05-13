all:
	happy -gca ParkCP.y
	alex -g LexkCP.x
	latex DockCP.tex; dvips DockCP.dvi -o DockCP.ps
	ghc --make interpreter.hs -o interpreter
clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f DockCP.ps
distclean: clean
	-rm -f DockCP.* LexkCP.* ParkCP.* LayoutkCP.* SkelkCP.* PrintkCP.* interpreter.* AbskCP.* Interpreter ErrM.* SharedString.* kCP.dtd XMLkCP.* Makefile*

