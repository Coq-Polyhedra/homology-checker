Require Import PArray Uint63.
From Bignums Require Import BigN BigZ BigQ.
From BinReader Require Import BinReader.

Time LoadData "../lrs-postprocess/data/cross3-cert.bin" As cert.

Section Inspect.

Let ineq := fst cert.
Let vert := fst (snd cert).
Let graph := fst (fst (snd (snd cert))).
Let lbl := snd (fst (snd (snd cert))).
Let root := snd (snd (snd cert)).

Check ineq.
Check vert.
Check graph.
Check lbl.
Check root.

Eval vm_compute in PArray.length ineq.
Eval vm_compute in PArray.length vert.
Eval vm_compute in PArray.length graph.
Eval vm_compute in PArray.length lbl.

End Inspect.
