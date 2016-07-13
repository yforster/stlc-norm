
stlc-norm : StlcNormalizing.fst
	fstar.exe $^

stlc-base : StlcCbvDbParSubst.fst
	fstar.exe StlcCbvDbParSubst.fst
