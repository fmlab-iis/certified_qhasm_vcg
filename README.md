
# Compilation Instructions #

1. Install (opam)[https://opam.ocaml.org].
   Follow the instructions in the
   (installation page)[https://opam.ocaml.org/doc/Install.html].

2. Configure opam.
```
    $ opam init
    $ eval $(opam env)
```

3. Switch OCaml version.
```
    $ opam switch create 4.07.1
    $ eval $(opam env)
```

4. Add additional opam repositories.
```
    $ opam repo add coq-released https://coq.inria.fr/opam/released
    $ opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
```

5. Install Coq.
```
    $ opam pin add coq 8.9.1
```

6. Install mathcomp and other Coq packages.
```
    $ opam install coq-mathcomp-ssreflect coq-mathcomp-algebra
    $ opam pin add lwt 5.0.1
    $ opam install lwt_ppx
```

7. Install external tools.
```
    $ sudo apt install singular boolector
```

8. Compile submodules.
```
    $ git submodule update --init --recursive
    $ make -C lib/gbarith
    $ make -C lib/polyop
    $ make -C lib/coq-bits
```

9. Compile Coq code.
``` 
    $ make
```

