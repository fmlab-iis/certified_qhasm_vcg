
From Coq Require Import BinNums.
From mathcomp Require Import ssreflect ssrbool seq.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(** Options *)

(*
  - opt_z3: use Z3 for QFBV solving
  - opt_boolector: use boolector for QFBV solving
  - opt_split: split postcondition at specification level,
               good for slicing, bad for rewriting a lot of assignments
  - opt_slicing: apply slicing before converting to SSA
  - opt_to_assign: convert equations (e1 = e2) to assignment form (x = e)
  - opt_keep_unused: do not convert (hi*2^w + lo = e) to (lo = e - hi*2^w)
                     if lo is not used but hi is used
  - opt_rewrite_assign: rewrite x = e and clear it
  - opt_rewrite_equality: rewrite e1 = e2
  - opt_lazy: use Lazy to do simplification
  - opt_native: use native_compute to do simplification
  - opt_singular: use Singular to do polynomial operations
  - opt_magma: use Magma to do polynomial operations
  - opt_isafety: split conjunctions when verifying safety and range conditions
  - opt_jobs: number of parallel jobs
  - opt_profiling: print some timing information
*)
Record verify_options : Set :=
  mkOptions { opt_z3 : bool;
              opt_boolector : bool;
              opt_split : bool;
              opt_slicing : bool;
              opt_to_assign : bool;
              opt_keep_unused : bool;
              opt_rewrite_assign : bool;
              opt_rewrite_equality : bool;
              opt_lazy : bool;
              opt_native : bool;
              opt_singular : bool;
              opt_magma : bool;
              opt_isafety: bool;
              opt_jobs : positive;
              opt_profiling : bool }.

Definition default_options : verify_options :=
  {| opt_z3 := false;
     opt_boolector := true;
     opt_split := true;
     opt_slicing := false;
     opt_to_assign := true;
     opt_keep_unused := false;
     opt_rewrite_assign := true;
     opt_rewrite_equality := true;
     opt_lazy := false;
     opt_native := true;
     opt_singular := true;
     opt_magma := false;
     opt_isafety := false;
     opt_jobs := 1;
     opt_profiling := true |}.

Inductive bool_flag : Set :=
| Z3
| Boolector
| Split
| Slicing
| ToAssign
| KeepUnused
| RewriteAssign
| RewriteEquality
| Lazy
| Native
| Singular
| Magma
| Isafety
| Profiling.

Inductive positive_flag : Set :=
| Jobs.

Inductive vflag : Set :=
| With : bool_flag -> vflag
| Without : bool_flag -> vflag
| Positive : positive_flag -> positive -> vflag.

Definition set_bool_flag f b o : verify_options :=
  match f with
  | Z3 => {| opt_z3 := b;
             opt_boolector := ~~b;
             opt_split := opt_split o;
             opt_slicing := opt_slicing o;
             opt_to_assign := opt_to_assign o;
             opt_keep_unused := opt_keep_unused o;
             opt_rewrite_assign := opt_rewrite_assign o;
             opt_rewrite_equality := opt_rewrite_equality o;
             opt_lazy := opt_lazy o;
             opt_native := opt_native o;
             opt_singular := opt_singular o;
             opt_magma := opt_magma o;
             opt_isafety := opt_isafety o;
             opt_jobs := opt_jobs o;
             opt_profiling := opt_profiling o |}
  | Boolector => {| opt_z3 := ~~b;
                    opt_boolector := b;
                    opt_split := opt_split o;
                    opt_slicing := opt_slicing o;
                    opt_to_assign := opt_to_assign o;
                    opt_keep_unused := opt_keep_unused o;
                    opt_rewrite_assign := opt_rewrite_assign o;
                    opt_rewrite_equality := opt_rewrite_equality o;
                    opt_lazy := opt_lazy o;
                    opt_native := opt_native o;
                    opt_singular := opt_singular o;
                    opt_magma := opt_magma o;
                    opt_isafety := opt_isafety o;
                    opt_jobs := opt_jobs o;
                    opt_profiling := opt_profiling o |}
  | Split => {| opt_z3 := opt_z3 o;
                opt_boolector := opt_boolector o;
                opt_split := b;
                opt_slicing := opt_slicing o;
                opt_to_assign := opt_to_assign o;
                opt_keep_unused := opt_keep_unused o;
                opt_rewrite_assign := opt_rewrite_assign o;
                opt_rewrite_equality := opt_rewrite_equality o;
                opt_lazy := opt_lazy o;
                opt_native := opt_native o;
                opt_singular := opt_singular o;
                opt_magma := opt_magma o;
                opt_isafety := opt_isafety o;
                opt_jobs := opt_jobs o;
                opt_profiling := opt_profiling o |}
  | Slicing => {| opt_z3 := opt_z3 o;
                  opt_boolector := opt_boolector o;
                  opt_split := opt_split o;
                  opt_slicing := b;
                  opt_to_assign := opt_to_assign o;
                  opt_keep_unused := opt_keep_unused o;
                  opt_rewrite_assign := opt_rewrite_assign o;
                  opt_rewrite_equality := opt_rewrite_equality o;
                  opt_lazy := opt_lazy o;
                  opt_native := opt_native o;
                  opt_singular := opt_singular o;
                  opt_magma := opt_magma o;
                  opt_isafety := opt_isafety o;
                  opt_jobs := opt_jobs o;
                  opt_profiling := opt_profiling o |}
  | ToAssign => {| opt_z3 := opt_z3 o;
                   opt_boolector := opt_boolector o;
                   opt_split := opt_split o;
                   opt_slicing := opt_slicing o;
                   opt_to_assign := b;
                   opt_keep_unused := opt_keep_unused o;
                   opt_rewrite_assign := opt_rewrite_assign o;
                   opt_rewrite_equality := opt_rewrite_equality o;
                   opt_lazy := opt_lazy o;
                   opt_native := opt_native o;
                   opt_singular := opt_singular o;
                   opt_magma := opt_magma o;
                   opt_isafety := opt_isafety o;
                   opt_jobs := opt_jobs o;
                   opt_profiling := opt_profiling o |}
  | KeepUnused => {| opt_z3 := opt_z3 o;
                     opt_boolector := opt_boolector o;
                     opt_split := opt_split o;
                     opt_slicing := opt_slicing o;
                     opt_to_assign := opt_to_assign o;
                     opt_keep_unused := b;
                     opt_rewrite_assign := opt_rewrite_assign o;
                     opt_rewrite_equality := opt_rewrite_equality o;
                     opt_lazy := opt_lazy o;
                     opt_native := opt_native o;
                     opt_singular := opt_singular o;
                     opt_magma := opt_magma o;
                     opt_isafety := opt_isafety o;
                     opt_jobs := opt_jobs o;
                     opt_profiling := opt_profiling o |}
  | RewriteAssign => {| opt_z3 := opt_z3 o;
                        opt_boolector := opt_boolector o;
                        opt_split := opt_split o;
                        opt_slicing := opt_slicing o;
                        opt_to_assign := opt_to_assign o;
                        opt_keep_unused := opt_keep_unused o;
                        opt_rewrite_assign := b;
                        opt_rewrite_equality := opt_rewrite_equality o;
                        opt_lazy := opt_lazy o;
                        opt_native := opt_native o;
                        opt_singular := opt_singular o;
                        opt_magma := opt_magma o;
                        opt_isafety := opt_isafety o;
                        opt_jobs := opt_jobs o;
                        opt_profiling := opt_profiling o |}
  | RewriteEquality => {| opt_z3 := opt_z3 o;
                          opt_boolector := opt_boolector o;
                          opt_split := opt_split o;
                          opt_slicing := opt_slicing o;
                          opt_to_assign := opt_to_assign o;
                          opt_keep_unused := opt_keep_unused o;
                          opt_rewrite_assign := opt_rewrite_assign o;
                          opt_rewrite_equality := b;
                          opt_lazy := opt_lazy o;
                          opt_native := opt_native o;
                          opt_singular := opt_singular o;
                          opt_magma := opt_magma o;
                          opt_isafety := opt_isafety o;
                          opt_jobs := opt_jobs o;
                          opt_profiling := opt_profiling o |}
  | Lazy => {| opt_z3 := opt_z3 o;
               opt_boolector := opt_boolector o;
               opt_split := opt_split o;
               opt_slicing := opt_slicing o;
               opt_to_assign := opt_to_assign o;
               opt_keep_unused := opt_keep_unused o;
               opt_rewrite_assign := opt_rewrite_assign o;
               opt_rewrite_equality := opt_rewrite_equality o;
               opt_lazy := b;
               opt_native := ~~b;
               opt_singular := opt_singular o;
               opt_magma := opt_magma o;
               opt_isafety := opt_isafety o;
               opt_jobs := opt_jobs o;
               opt_profiling := opt_profiling o |}
  | Native => {| opt_z3 := opt_z3 o;
                 opt_boolector := opt_boolector o;
                 opt_split := opt_split o;
                 opt_slicing := opt_slicing o;
                 opt_to_assign := opt_to_assign o;
                 opt_keep_unused := opt_keep_unused o;
                 opt_rewrite_assign := opt_rewrite_assign o;
                 opt_rewrite_equality := opt_rewrite_equality o;
                 opt_lazy := ~~b;
                 opt_native := b;
                 opt_singular := opt_singular o;
                 opt_magma := opt_magma o;
                 opt_isafety := opt_isafety o;
                 opt_jobs := opt_jobs o;
                 opt_profiling := opt_profiling o |}
  | Singular => {| opt_z3 := opt_z3 o;
                   opt_boolector := opt_boolector o;
                   opt_split := opt_split o;
                   opt_slicing := opt_slicing o;
                   opt_to_assign := opt_to_assign o;
                   opt_keep_unused := opt_keep_unused o;
                   opt_rewrite_assign := opt_rewrite_assign o;
                   opt_rewrite_equality := opt_rewrite_equality o;
                   opt_lazy := opt_lazy o;
                   opt_native := opt_native o;
                   opt_singular := b;
                   opt_magma := ~~b;
                   opt_isafety := opt_isafety o;
                   opt_jobs := opt_jobs o;
                   opt_profiling := opt_profiling o |}
  | Magma => {| opt_z3 := opt_z3 o;
                opt_boolector := opt_boolector o;
                opt_split := opt_split o;
                opt_slicing := opt_slicing o;
                opt_to_assign := opt_to_assign o;
                opt_keep_unused := opt_keep_unused o;
                opt_rewrite_assign := opt_rewrite_assign o;
                opt_rewrite_equality := opt_rewrite_equality o;
                opt_lazy := opt_lazy o;
                opt_native := opt_native o;
                opt_singular := ~~b;
                opt_magma := b;
                opt_isafety := opt_isafety o;
                opt_jobs := opt_jobs o;
                opt_profiling := opt_profiling o |}
  | Isafety => {| opt_z3 := opt_z3 o;
                  opt_boolector := opt_boolector o;
                  opt_split := opt_split o;
                  opt_slicing := opt_slicing o;
                  opt_to_assign := opt_to_assign o;
                  opt_keep_unused := opt_keep_unused o;
                  opt_rewrite_assign := opt_rewrite_assign o;
                  opt_rewrite_equality := opt_rewrite_equality o;
                  opt_lazy := opt_lazy o;
                  opt_native := opt_native o;
                  opt_singular := opt_singular o;
                  opt_magma := opt_magma o;
                  opt_isafety := b;
                  opt_jobs := opt_jobs o;
                  opt_profiling := opt_profiling o |}
  | Profiling => {| opt_z3 := opt_z3 o;
                    opt_boolector := opt_boolector o;
                    opt_split := opt_split o;
                    opt_slicing := opt_slicing o;
                    opt_to_assign := opt_to_assign o;
                    opt_keep_unused := opt_keep_unused o;
                    opt_rewrite_assign := opt_rewrite_assign o;
                    opt_rewrite_equality := opt_rewrite_equality o;
                    opt_lazy := opt_lazy o;
                    opt_native := opt_native o;
                    opt_singular := opt_singular o;
                    opt_magma := opt_magma o;
                    opt_isafety := opt_isafety o;
                    opt_jobs := opt_jobs o;
                    opt_profiling := b |}
  end.

Definition set_positive_flag f i o : verify_options :=
  match f with
  | Jobs => {| opt_z3 := opt_z3 o;
               opt_boolector := opt_boolector o;
               opt_split := opt_split o;
               opt_slicing := opt_slicing o;
               opt_to_assign := opt_to_assign o;
               opt_keep_unused := opt_keep_unused o;
               opt_rewrite_assign := opt_rewrite_assign o;
               opt_rewrite_equality := opt_rewrite_equality o;
               opt_lazy := opt_lazy o;
               opt_native := opt_native o;
               opt_singular := opt_singular o;
               opt_magma := opt_magma o;
               opt_isafety := opt_isafety o;
               opt_jobs := i;
               opt_profiling := opt_profiling o |}
  end.

Definition set_vflag f o : verify_options :=
  match f with
  | With g => set_bool_flag g true o
  | Without g => set_bool_flag g false o
  | Positive g i => set_positive_flag g i o
  end.

Definition oconf_with flags o : verify_options :=
  foldr set_vflag o flags.

(* Configure options based on default settings. *)
Definition oconf flags : verify_options :=
  oconf_with flags default_options.
