testGHC: process_rusage.o TestGHC.hs TestGHCMain.hs
	ghc --make -o testGHC TestGHCMain.hs process_rusage.o -O2

testGHC_p: process_rusage.o TestGHC.hs TestGHCMain.hs
	ghc --make -o testGHC_p TestGHCMain.hs process_rusage.o -O0 -prof -auto-all -caf-all
