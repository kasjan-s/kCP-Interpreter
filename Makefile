all:
	happy -gca ParkCP.y
	alex -g LexkCP.x
	latex DockCP.tex; dvips DockCP.dvi -o DockCP.ps
	ghc --make TestkCP.hs -o TestkCP
clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f DockCP.ps
distclean: clean
	-rm -f DockCP.* LexkCP.* ParkCP.* LayoutkCP.* SkelkCP.* PrintkCP.* TestkCP.* AbskCP.* TestkCP ErrM.* SharedString.* kCP.dtd XMLkCP.* Makefile*

