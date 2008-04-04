(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.11                                 *)
(*                              Feb 2nd 1996                                *)
(*                                                                          *)
(****************************************************************************)
(*                               Functions.v                                *)
(****************************************************************************)

Require Import Ensembles.    (* Ensemble, In, Included, Setminus *)
Require Import Relations_1.  (* Relation *)

(************************************************************************)
(* In contrast with the definition of functions in Relations_1, we      *)
(* consider, here, functions as binary relations                        *)

Section Functions.

Variable U : Type.

(************************************************************************)
(* Characterization of a relation over two sets                         *)
(* Caracterisation d'une relation d'un ensemble donne dans un autre     *)

Inductive Rel (U : Type) (A B : Ensemble U) (R : Relation U) : Prop :=
    Rel_intro :
      (forall x y : U, R x y -> In U A x) ->
      (forall x y : U, R x y -> In U B y) -> Rel U A B R.
 

(************************************************************************)
(*              Image of a set through a relation                       *)

Section Image.

Inductive Im (R : Relation U) (A : Ensemble U) (y : U) : Prop :=
    Im_intro : forall x : U, R x y -> In U A x -> Im R A y.

Lemma Im_stable_par_incl :
 forall (R : Relation U) (A1 A2 : Ensemble U),
 Included U A1 A2 -> Included U (Im R A1) (Im R A2).
do 3 intro; intros A1_Included_A2; red in |- *; red in |- *;
 intros x x_in_Im_A1.
elim x_in_Im_A1.
intros.
apply Im_intro with x0; try assumption.
apply A1_Included_A2; assumption.
Qed.

End Image.


Variable A B : Ensemble U.
Variable f : Relation U.


Definition au_plus_une_im := forall x y z : U, f x y -> f x z -> y = z.

Definition au_moins_une_im := forall x : U, In U A x -> ex (f x).

Definition au_plus_un_ant := forall x y z : U, f x z -> f y z -> x = y.

Definition au_moins_un_ant := forall y : U, In U B y -> exists x : U, f x y.


Inductive fonction : Prop := (* fun_in *)
    fonction_intro :
      Rel U A B f -> au_plus_une_im -> au_moins_une_im -> fonction.

Inductive surjection : Prop := (* fun_on *)
    surjection_intro :
      Rel U A B f ->
      au_plus_une_im -> au_moins_une_im -> au_moins_un_ant -> surjection.

Inductive injection : Prop := (* map_in *)
    injection_intro :
      Rel U A B f ->
      au_plus_une_im -> au_moins_une_im -> au_plus_un_ant -> injection.

Inductive bijection : Prop := (* map_on *)
    bijection_intro :
      Rel U A B f ->
      au_plus_une_im ->
      au_moins_une_im -> au_plus_un_ant -> au_moins_un_ant -> bijection.

End Functions.


(* $Id$ *)