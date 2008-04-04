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
(*                            Setminus_fact.v                               *)
(****************************************************************************)

Require Import Ensembles.    (* Ensemble, In, Included, Setminus *)

Section Contravariance_of_Setminus.

Variable U : Type.

Lemma Setminus_contravariant :
 forall A B B' : Ensemble U,
 Included U B' B -> Included U (Setminus U A B) (Setminus U A B').
intros A B B' B'_Included_B; unfold Setminus in |- *.
red in |- *; intros x x_in_B.
elim x_in_B; intros x_in_A x_in_nonB.
split.
  assumption.
red in |- *; intro x_in_B'.
apply x_in_nonB.
apply B'_Included_B.
assumption.
Qed.

End Contravariance_of_Setminus.


(* $Id$ *)