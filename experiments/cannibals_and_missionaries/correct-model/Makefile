
Z3_OPTS = -v:10 -st 
Z3 = z3 $(Z3_OPTS)

all: pfs vfs

pfs:
				$(Z3) pfs.smt2 > pfs.out 2> pfs.err

vfs:
				$(Z3) vfs.smt2 > vfs.out 2> vfs.err

clean:
				rm -rf *~ *.out *.err
