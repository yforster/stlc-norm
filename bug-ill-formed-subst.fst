module StlcNormalizing

open StlcCbvDbParSubst
open Constructive
       
kind Relation (a:Type) = a -> a -> Type
type multi (a:Type) (r:Relation a) : a -> a -> Type =
| Multi_refl : x:a -> multi a r x x
| Multi_step : x:a -> y:a -> z:a -> r x y -> multi a r y z -> multi a r x z
type steps : exp -> exp -> Type = fun x y -> multi exp step x y
type halts (e:exp) : Type = cexists (fun e' -> u:(steps e e'){is_value e'})

(* This has a negative occurrence of R that makes Coq succumb,
although this definition is just fine (the type decreases);
F* should have similar problems as soon as we start checking
for negative occurrences. Hopefully by then we will also have
a solution for this. *)
type red : typ -> exp -> Type =
(* | R_bool : e:exp -> typing empty e TBool -> halts e -> red TBool e *)
| R_arrow : t1:typ -> t2:typ -> #e:exp ->
            typing empty e (TArr t1 t2) ->
            halts e ->
            (e':exp -> red t1 e' -> Tot (red t2 (EApp e e'))) ->
            red (TArr t1 t2) e     
                      
val red_subst : g:env -> e:exp -> t:typ -> sigma:sub ->
                typing g e t ->
                red2 g sigma ->
                typing empty (subst sigma e) t
let red_subst g e t sigma ty_t r = substitution_lemma empty sigma ty_t
                                        (fun x t ->
                                         let Conj r1 r2 = r in
                                         let ExIntro s h1 = r1 x t in
                                         ExIntro s (red_typable_empty h1))

type ered (t : typ) (e : exp) = e':exp -> step e e' -> red t e'

val red_term_ap : t1:typ -> t2:typ -> e:exp{not (is_value e)} ->
                  (u:exp -> typing empty u t2 -> ered t2 u ->
                   Tot (red t2 u) (requires (not (is_value u))) (ensures True)) ->
                  typing empty e (TArr t1 t2) ->
                  ered (TArr t1 t2) e ->
                  e':exp -> red t1 e' -> Tot (red t2 (EApp e e'))
let red_term_ap t1 t2 e f ered_t1_t2 e' r_t1 =
  (* let ExIntro v h = red_halts red_e' in *)
  (* let rec induction (h : steps e' v) : red t2 (EApp e e') = admit() *)
  (* in *)
  (* induction h *)
  magic()
