Require Import Rgeom.
Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo1.
Require Import R_sqrt.
Local Open Scope R_scope.

Lemma triangle2 :
  forall x0 y0 x1 y1 x2 y2:R,
    dist_euc x0 y0 x1 y1 <= dist_euc x0 y0 x2 y2 + dist_euc x2 y2 x1 y1.
Proof.
