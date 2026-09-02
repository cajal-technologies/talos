import CodeLib
open Iris Iris.BI
variable {GF : BundledGFunctors}
example (A B C D E F G H Z : IProp GF) :
    (A -∗ B -∗ C -∗ D -∗ E -∗ F -∗ G -∗ H -∗ Z) ⊢
    (A -∗ B -∗ C -∗ D -∗ E -∗ F -∗ G -∗ H -∗ Z) := by
  iintro Hall
  iintro HA HB HC HD HE HF HG HH
  iapply Hall $$ HA HB HC HD HE HF HG HH

example (A B C D E F G H Z : IProp GF) :
    (A -∗ B -∗ C -∗ D -∗ E -∗ F -∗ G -∗ H -∗ Z) ⊢
    (A -∗ B -∗ C -∗ D -∗ E -∗ F -∗ G -∗ H -∗ Z) := by
  iintro Hall
  iintro HA
  iintro HB
  iintro HC
  iintro HD
  iintro HE
  iintro HF
  iintro HG
  iintro HH
  iapply Hall $$ HA HB HC HD HE HF HG HH
