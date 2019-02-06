Z3_OPTS = -v:10 -st 
Z3 = z3 $(Z3_OPTS)

all: pfs

pfs:
				$(Z3) pfs.smt2 > pfs.out 2> pfs.err

pfs2:
				$(Z3) pfs_tranz_only.smt2 > pfs_tranz_only.out 2> vfs_tranz_only.err

clean:
				rm -rf *~ *.out *.err
