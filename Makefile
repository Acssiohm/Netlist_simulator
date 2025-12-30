build :
	opam exec dune -- build  # pas nécessaire, c'est juste pour l'AST
	ocamlbuild netlist_simulator.byte 

% : %.net
	./netlist_simulator.byte $@.net

clean :
	opam exec dune -- clean
	rm -f ./test/*_sch.net
	rm ./netlist_simulator.byte

.PHONY : clean, build