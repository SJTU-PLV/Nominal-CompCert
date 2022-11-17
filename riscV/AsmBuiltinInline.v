Require Import Coqlib Integers AST Memdata Maps.
Require Import Asm Asmgen.
Require Import Errors.
Require Import Memory.
Require Import TargetPrinterAux AsmLabelNew.
Import ListNotations.

Local Open Scope error_monad_scope.

(* Handling of memcpy *)

Definition offset_in_range ofs :=
  let ofs := Ptrofs.signed ofs in
  (-2048 <=? ofs) && (ofs <? 2048).

Definition memcpy_small_arg (sz: Z) (arg :builtin_arg preg) (tmp: ireg) : res (ireg * ptrofs * list instruction) :=
  match arg with
  | BA (IR r) =>
    OK (r, Ptrofs.zero , [])
  | BA_addrstack ofs =>
    if offset_in_range ofs && offset_in_range (Ptrofs.add ofs  (Ptrofs.repr sz)) then
      OK (X2, ofs, [])
    else OK (tmp, Ptrofs.zero, expand_addptrofs tmp X2 ofs)
  | _ => Error (msg "RISCV: memcpy_small_arg")
  end.

Fixpoint copy (fuel:nat) (rsrc rdst: ireg) (al: Z) (osrc odst: ptrofs) (sz :Z) : list instruction :=
  match fuel with
  | O => []
  | S fuel' =>
    let copy := copy fuel' rsrc rdst al in
    if (sz >=? 8) && (al >=? 8) then
      [Pfld F0 rsrc (Ofsimm osrc); Pfsd F0 rdst (Ofsimm odst)] ++ (copy (Ptrofs.add osrc (Ptrofs.repr 8)) (Ptrofs.add odst (Ptrofs.repr 8)) (sz - 8))
    else
      if (sz >=? 4) && (al >=? 4) then
        [Plw X31 rsrc (Ofsimm osrc); Psw X31 rdst (Ofsimm odst)] ++ (copy (Ptrofs.add osrc (Ptrofs.repr 4)) (Ptrofs.add odst (Ptrofs.repr 4)) (sz - 4))
      else if (sz >=? 2) && (al >=? 2) then
             [Plh X31 rsrc (Ofsimm osrc); Psh X31 rdst (Ofsimm odst)] ++ (copy (Ptrofs.add osrc (Ptrofs.repr 2)) (Ptrofs.add odst (Ptrofs.repr 2)) (sz - 2))
           else if (sz >=? 1) then
                  [Plb X31 rsrc (Ofsimm osrc); Psb X31 rdst (Ofsimm odst)] ++ (copy (Ptrofs.add osrc (Ptrofs.repr 1)) (Ptrofs.add odst (Ptrofs.repr 1)) (sz - 1))
                else []
  end.


Definition expand_builtin_memcpy_small (sz al:Z) (src dst:builtin_arg preg) :=
  let (tsrc, tdst) :=
      match dst with
      | BA (IR X5) => (X5, X6)
      | _ => (X6, X5) end in
  do (rsrc_osrc, i1) <- memcpy_small_arg sz src tsrc;
  do (rdst_odst, i2) <- memcpy_small_arg sz dst tdst;
  let (rsrc, osrc) := rsrc_osrc in
  let (rdst, odst) := rdst_odst in
  OK (i1 ++ i2 ++ copy (Z.to_nat sz) rsrc rdst al osrc odst sz).

Definition memcpy_big_arg (sz:Z) (arg:builtin_arg preg) (tmp: ireg) : res (list instruction) :=
  match arg with
  | BA (IR r) =>
    OK (if ireg_eq r tmp then []
        else [Pmv tmp r])
  | BA_addrstack ofs =>
    OK (expand_addptrofs tmp X2 ofs)
  | _ => Error (msg"RISCV: memcpy_big_arg")
  end.

Definition expand_builtin_memcpy_big (sz al: Z) (src dst: builtin_arg preg) :=
  if (sz <? al) || negb (sz mod al =? 0) then
    Error (msg"sz < al or sz mod al <> = 0 in expand_builtin_memcpy_big")
  else
    let (s,d) :=
        match dst with
        | BA (IR X5) => (X5, X6)
        | _ => (X6, X5) end in
    do i1 <- memcpy_big_arg sz src s;
    do i2 <- memcpy_big_arg sz dst d;
    let '(load, store, chunksize) :=
        if al >=? 8 then
          (Pfld F0 s (Ofsimm Ptrofs.zero), Pfsd F0 d (Ofsimm Ptrofs.zero), 8)
        else if al >=? 4 then
               (Plw X31 s (Ofsimm Ptrofs.zero), Psw X31 d (Ofsimm Ptrofs.zero), 4)
             else if al =? 2 then
                    (Plh X31 s (Ofsimm Ptrofs.zero), Psh X31 d (Ofsimm Ptrofs.zero), 2)
                  else
                    (Plb X31 s (Ofsimm Ptrofs.zero), Psb X31 d (Ofsimm Ptrofs.zero), 1) in
    let count := expand_loadimm32 X7 (Int.repr (sz / chunksize)) in
    let delta := Ptrofs.repr chunksize in
    let lbl := new_label tt in
    let label := [Plabel lbl] in
    let accsrc := expand_addptrofs s s delta in
    let decrement := [Paddiw X7 (X X7) (Int.repr (-1))] in
    let accdst := expand_addptrofs d d delta in
    let branchlbl := [Pbnew (X X7) X0 lbl] in
    OK (i1 ++ i2 ++ count ++ label ++ [load] ++ accsrc ++ decrement ++ [store] ++ accdst ++ branchlbl).
    
Definition expand_builtin_memcpy (sz al: Z) (args: list (builtin_arg preg)) : res (list instruction) :=
  do (dst,src) <- match args with
                   | [d;s] => OK (d,s)
                   | _ => Error (msg "args error in expand_builtin_memcpy")
                 end;
  if sz <=? 32 then
    expand_builtin_memcpy_small sz al src dst
  else
    expand_builtin_memcpy_big sz al src dst.
      
(* Handling of volatile reads and writes *)

Definition expand_builtin_vload_common (chunk: memory_chunk) (base: ireg) (ofs: ptrofs) (res_reg: builtin_res preg) : res (list instruction) :=
  match chunk, res_reg with
  | Mint8unsigned, BR (IR res) =>
    OK [Plbu res base (Ofsimm ofs)]
  | Mint8signed, BR (IR res) =>
    OK [Plb res base (Ofsimm ofs)]
  | Mint16unsigned, BR (IR res) =>
    OK [Plhu res base (Ofsimm ofs)]
  | Mint16signed, BR (IR res) =>
    OK [Plh res base (Ofsimm ofs)]
  | Mint32, BR (IR res) =>
    OK [Plw res base (Ofsimm ofs)]
  | Mint64, BR (IR res) =>
    OK [Pld res base (Ofsimm ofs)]
  | Mint64, BR_splitlong (BR (IR res1)) (BR (IR res2)) =>
    let ofs' := Ptrofs.add ofs (Ptrofs.repr 4) in
    if ireg_eq base res2 then
      OK [Plw res1 base (Ofsimm ofs'); Plw res2 base (Ofsimm ofs)]
    else
      OK [Plw res2 base (Ofsimm ofs); Plw res1 base (Ofsimm ofs')]
  | Mfloat32, BR (FR res) =>
    OK [Pfls res base (Ofsimm ofs)]
  | Mfloat64, BR (FR res) =>
    OK [Pfld res base (Ofsimm ofs)]
  | _,_ => Error(msg"expand_builtin_vload_common")
  end.


Definition expand_builtin_vload (chunk: memory_chunk) (args: list (builtin_arg preg)) (res: builtin_res preg) :=
  match args with
  | [BA (IR addr)] =>
    expand_builtin_vload_common chunk addr (Ptrofs.zero) res
  | [BA_addrstack ofs] =>
    if offset_in_range (Ptrofs.add ofs (Ptrofs.repr (size_chunk chunk))) then
      expand_builtin_vload_common chunk X2 ofs res
    else
      do load <- expand_builtin_vload_common chunk X31 Ptrofs.zero res;
      OK (expand_addptrofs X31 X2 ofs ++ load)
  | [BA_addptr (BA (IR addr)) (BA_int ofs)] =>
    let ofs := Ptrofs.repr (Int.signed ofs) in
    if offset_in_range (Ptrofs.add ofs (Ptrofs.repr (size_chunk chunk))) then
      expand_builtin_vload_common chunk addr ofs res
    else
      do load <- expand_builtin_vload_common chunk X31 Ptrofs.zero res;
      OK (expand_addptrofs X31 addr ofs ++ load)
  | [BA_addptr (BA (IR addr)) (BA_long ofs)] =>
    let ofs := Ptrofs.repr (Int64.signed ofs) in
    if offset_in_range (Ptrofs.add ofs (Ptrofs.repr (size_chunk chunk))) then
      expand_builtin_vload_common chunk addr ofs res
    else
      do load <- expand_builtin_vload_common chunk X31 Ptrofs.zero res;
      OK (expand_addptrofs X31 addr ofs ++ load)
  | _ => Error (msg "expand_builtin_vload")
  end.

Definition expand_builtin_vstore_common (chunk: memory_chunk) (base: ireg) (ofs: ptrofs) (src: builtin_arg preg) : res (list instruction) :=
  match chunk, src with
  | Mint8unsigned, BA (IR src) =>
    OK [Psb src base (Ofsimm ofs)]
  | Mint8signed, BA (IR src) =>
    OK [Psb src base (Ofsimm ofs)]
  | Mint16unsigned, BA (IR src) =>
    OK [Psh src base (Ofsimm ofs)]
  | Mint16signed, BA (IR src) =>
    OK [Psh src base (Ofsimm ofs)]
  | Mint32, BA (IR src) =>
    OK [Psw src base (Ofsimm ofs)]
  | Mint64, BA (IR src) =>
    OK [Psd src base (Ofsimm ofs)]
  | Mint64, BA_splitlong (BA (IR src1)) (BA (IR src2)) =>
    let ofs' := Ptrofs.add ofs (Ptrofs.repr 4) in
      OK [Psw src2 base (Ofsimm ofs); Plw src1 base (Ofsimm ofs')]
  | Mfloat32, BA (FR src) =>
    OK [Pfls src base (Ofsimm ofs)]
  | Mfloat64, BA (FR src) =>
    OK [Pfld src base (Ofsimm ofs)]
  | _,_ => Error(msg"expand_builtin_vstore_common")
  end.


Definition expand_builtin_vstore (chunk: memory_chunk) (args: list (builtin_arg preg)) :=
  match args with
  | [BA (IR addr); src] =>
    expand_builtin_vstore_common chunk addr (Ptrofs.zero) src
  | [BA_addrstack ofs; src] =>
    if offset_in_range (Ptrofs.add ofs (Ptrofs.repr (size_chunk chunk))) then
      expand_builtin_vstore_common chunk X2 ofs src
    else
      do store <- expand_builtin_vstore_common chunk X31 Ptrofs.zero src;
      OK (expand_addptrofs X31 X2 ofs ++ store)
  | [BA_addptr (BA (IR addr)) (BA_int ofs); src] =>
    let ofs := Ptrofs.repr (Int.signed ofs) in
    if offset_in_range (Ptrofs.add ofs (Ptrofs.repr (size_chunk chunk))) then
      expand_builtin_vstore_common chunk addr ofs src
    else
      do store <- expand_builtin_vstore_common chunk X31 Ptrofs.zero src;
      OK (expand_addptrofs X31 addr ofs ++ store)
  | [BA_addptr (BA (IR addr)) (BA_long ofs); src] =>
    let ofs := Ptrofs.repr (Int64.signed ofs) in
    if offset_in_range (Ptrofs.add ofs (Ptrofs.repr (size_chunk chunk))) then
      expand_builtin_vstore_common chunk addr ofs src
    else
      do store <- expand_builtin_vstore_common chunk X31 Ptrofs.zero src;
      OK (expand_addptrofs X31 addr ofs ++ store)
  | _ => Error (msg "expand_builtin_vstore")
  end.

(* Handling of varargs *)

(* pass the current function to get the stacksize and signature *)
Definition expand_builtin_va_start (r: ireg) (f: function) :=
  let sg := f.(fn_sig) in
  let sz := f.(fn_stacksize) in
  match sg.(sig_cc).(cc_vararg) with
  | Some _ =>
    let n := arguments_size sg in
    let extra_size := if n >=? 8 then 0 else align ((8-n) * wordsize) 16 in
    let full_sz := Z.add sz extra_size in
    (* the starting offset of the va_list. It may be greater than full_sz  *)
    let va_ofs := Z.add full_sz ((n - 8) * wordsize) in
    OK (expand_addptrofs X31 X2 (Ptrofs.repr va_ofs) ++ expand_storeind_ptr X31 r Ptrofs.zero)
  | _ => Error(msg"Fatal error: va_start used in non-vararg function")
  end.
             
(* Auxiliary for 64-bit integer arithmetic built-ins. *)

Definition expand_int64_arith (conflict: bool) (rl: ireg) (fn: ireg -> list instruction) : list instruction :=
  if conflict then fn X31 ++ [Pmv rl X31] else fn rl.

(* Byte swaps.  There are no specific instructions, so we use standard, not-very-efficient formulas. *)

Definition expand_bswap16 (d s: ireg) :=
  (* d = (s & 0xFF) << 8 | (s >> 8) & 0xFF *)
  [Pandiw X31 (X s) (Int.repr 255);
  Pslliw X31 (X X31) (Int.repr 8);
  Psrliw d (X s) (Int.repr 8);
  Pandiw d (X d) (Int.repr 255);
  Porw d (X X31) (X d)].

Definition expand_bswap32 (d s: ireg) :=
  [(Pslliw X1 (X s) (Int.repr 24));
  (Psrliw X31 (X s) (Int.repr 8));
  (Pandiw X31 (X X31) (Int.repr 255));
  (Pslliw X31 (X X31) (Int.repr 16));
  (Porw X1 (X X1) (X X31));
  (Psrliw X31 (X s) (Int.repr 16));
  (Pandiw X31 (X X31) (Int.repr 255));
  (Pslliw X31 (X X31) (Int.repr 8));
  (Porw X1 (X X1) (X X31));
  (Psrliw X31 (X s) (Int.repr 24));
  (Porw d (X X1) (X X31))].

Definition expand_bswap64 d s :=
  let i1 := Psllil X1 (X s) (Int.repr 56) in
  let i2 := fold_left
              (fun acc p => [Psrlil X31 (X s) (Int.repr (fst p)); Pandil X31 (X X31) (Int64.repr 255); Psllil X31 (X X31) (Int.repr (snd p)); Porl X1 (X X1) (X X31)])
              [(8,48); (16,40); (24,32); (32,24); (40,16); (48,8)] [] in
  [i1] ++ i2 ++ [Psrlil X31 (X s) (Int.repr 56); Porl d (X X1) (X X31)].

(* Count leading zeros.  Algorithm 5-7 from Hacker's Delight,
   re-rolled as a loop to produce more compact code. *)

Definition expand_clz (sixtyfour splitlong: bool) : list instruction :=
    (* Input:  X in X5 or (X5, X6) if splitlong
     Result: N in X7
     Temporaries: S in X8, Y in X9 *)
  let lbl1 := new_label tt in
  let lbl2 := new_label tt in
  (* N := bitsize of X's type (32 or 64) *)
  expand_loadimm32 X7 (Int.repr
                         (if sixtyfour || splitlong then 64 else 32)) ++
  (* S := initial shift amount (16 or 32) *)                         
  expand_loadimm32 X8 (Int.repr (if sixtyfour then 32 else 16)) ++
  (if splitlong then
    (* if (Xhigh == 0) goto lbl1 *)
     [Pbeqw (X X6) X0 lbl1] ++
    (* N := 32 *)
    expand_loadimm32 X7 (Int.repr 32) ++
    (* X := Xhigh *)
    [Pmv X5 X6]
  else []) ++
  (* lbl1: *)
  [Plabel lbl1;
  (* Y := X >> S *)
  (if sixtyfour then Psrll X9 (X X5) (X X8) else Psrlw X9 (X X5) (X X8));
  (* if (Y == 0) goto lbl2 *)
  (if sixtyfour then Pbeql (X X9) X0 lbl2 else Pbeqw (X X9) X0 lbl2);
  (* N := N - S *)
  (Psubw X7 (X X7) (X X8));
  (* X := Y *)
  (Pmv X5 X9);
  (* lbl2: *)
  (Plabel lbl2);
  (* S := S / 2 *)
  (Psrliw X8 (X X8) (Int.repr 1));
  (* if (S != 0) goto lbl1; *)
  (Pbnew (X X8) X0 lbl1);
  (* N := N - X *)
  (Psubw X7 (X X7) (X X5))].

(* Count trailing zeros.  Algorithm 5-14 from Hacker's Delight,
   re-rolled as a loop to produce more compact code. *)

Definition expand_ctz (sixtyfour splitlong:bool) : list instruction :=
  (* Input:  X in X6 or (X5, X6) if splitlong
     Result: N in X7
     Temporaries: S in X8, Y in X9 *)
  let lbl1 := new_label tt in
  let lbl2 := new_label tt in
  (* N := bitsize of X's type (32 or 64) *)
  expand_loadimm32 X7 (Int.repr
                         (if sixtyfour || splitlong then 64 else 32)) ++
  (* S := initial shift amount (16 or 32) *)                         
  expand_loadimm32 X8 (Int.repr (if sixtyfour then 32 else 16)) ++
  (if splitlong then
    (* if (Xlow == 0) goto lbl1 *)
    [Pbeqw (X X5) X0 lbl1] ++
    (* N := 32 *)
    (expand_loadimm32 X7 (Int.repr 32)) ++
    (* X := Xlow *)
    [Pmv X6 X5]
   else []) ++
  (* lbl1: *)
  [Plabel lbl1;
  (* Y := X >> S *)
  if sixtyfour then Pslll X9 (X X6) (X X8) else Psllw X9 (X X6) (X X8);
  (* if (Y == 0) goto lbl2 *)
  if sixtyfour then Pbeql (X X9) X0 lbl2 else Pbeqw (X X9) X0 lbl2;
  (* N := N - S *)
  Psubw X7 (X X7) (X X8);
  (* X := Y *)
  Pmv X6 X9;
  (* lbl2: *)
  Plabel lbl2;
  (* S := S / 2 *)
  Psrliw X8 (X X8) (Int.repr 1);
  (* if (S != 0) goto lbl1; *)
  Pbnew (X X8) X0 lbl1;
  (* N := N - most significant bit of X *)
  if sixtyfour then Psrlil X6 (X X6) (Int.repr 63)
  else Psrliw X6 (X X6) (Int.repr 31);
  Psubw X7 (X X7) (X X6)].


(* Handling of compiler-inlined builtins *)
Definition expand_builtin_inline (f:function) (name: string) (args: list (builtin_arg preg)) (res: builtin_res preg) : Errors.res (list instruction) :=
  match name, args, res with
  | "__builtin_membar"%string, [], _ =>
    OK []
  | "__builtin_fence"%string, [], _ =>
     OK [Pfence]
  (* Vararg stuff *)
  | "__builtin_va_start"%string, [BA(IR a)], _ =>
     expand_builtin_va_start a f
  (* Byte swaps *)
  | "__builtin_bswap16"%string, [BA(IR a1)], BR(IR res) =>
     OK (expand_bswap16 res a1)
  | ("__builtin_bswap"%string| "__builtin_bswap32"%string), [BA(IR a1)], BR(IR res) =>
     OK (expand_bswap32 res a1)
  | "__builtin_bswap64"%string, [BA(IR a1)], BR(IR res) =>
     OK (expand_bswap64 res a1)
  | "__builtin_bswap64"%string, [BA_splitlong (BA(IR ah)) (BA(IR al))],
    BR_splitlong (BR (IR rh)) (BR (IR rl)) =>
    if ((ireg_eq ah X6) && (ireg_eq al X5) && (ireg_eq rh X5) && (ireg_eq rl X6)) then
      OK (expand_bswap32 X5 X5 ++ expand_bswap32 X6 X6)
    else
      Error (msg"expand_builtin_inline: __builtin_bswap64")
  (* Count zeros *)
  | "__builtin_clz"%string, [BA(IR a)], BR(IR res) =>
     if (ireg_eq a X5) && (ireg_eq res X7) then
       OK (expand_clz false false)
     else
       Error (msg"expand_builtin_inline: __builtin_clz")
  | "__builtin_clzl"%string, [BA(IR a)], BR(IR res) =>
     if (ireg_eq a X5) && (ireg_eq res X7) then
       OK (expand_clz Archi.ptr64 false)
     else
       Error (msg"expand_builtin_inline: __builtin_clzl")
  | "__builtin_clzll"%string, [BA(IR a)], BR(IR res) =>
     if (ireg_eq a X5) && (ireg_eq res X7) then
       OK (expand_clz true false)
     else
       Error (msg"expand_builtin_inline: __builtin_clzll")     
  | "__builtin_clzll"%string, [BA_splitlong (BA (IR ah))  (BA(IR al))], BR(IR res) =>
     if (ireg_eq al X5) && (ireg_eq ah X6) && (ireg_eq res X7) then
       OK (expand_clz false true)
     else
       Error (msg"expand_builtin_inline: __builtin_clzll splitlong")
  | "__builtin_ctz"%string, [BA(IR a)], BR(IR res) =>
     if (ireg_eq a X6) && (ireg_eq res X7) then
       OK (expand_ctz false false)
     else
       Error (msg"expand_builtin_inline: __builtin_ctz")       
  | "__builtin_ctzl"%string, [BA(IR a)], BR(IR res) =>
     if (ireg_eq a X6) && (ireg_eq res X7) then
       OK (expand_ctz Archi.ptr64 false)
     else
       Error (msg"expand_builtin_inline: __builtin_ctzl")
  | "__builtin_ctzll"%string, [BA(IR a)], BR(IR res) =>
     if (ireg_eq a X6) && (ireg_eq res X7) then
       OK (expand_ctz true false)
     else
       Error (msg"expand_builtin_inline: __builtin_ctzll")
  | "__builtin_ctzll"%string, [BA_splitlong (BA (IR ah)) (BA (IR al))], BR(IR res) =>
     if (ireg_eq al X5) && (ireg_eq ah X6) && (ireg_eq res X7) then
       OK (expand_ctz false true)
     else
       Error (msg"expand_builtin_inline: __builtin_ctzll")
  (* Float arithmetic *)
  | ("__builtin_fsqrt"%string | "__builtin_sqrt"%string), [BA(FR a1)], BR(FR res) =>
    OK [Pfsqrtd res a1]
  | "__builtin_fmadd"%string, [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) =>
    OK [Pfmaddd res a1 a2 a3]
  | "__builtin_fmsub"%string, [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) =>
    OK [Pfmsubd res a1 a2 a3]
  | "__builtin_fnmadd"%string, [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) =>
    OK  [Pfnmaddd res a1 a2 a3]
  | "__builtin_fnmsub"%string, [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) =>
    OK [Pfnmsubd res a1 a2 a3]
  | "__builtin_fmin"%string, [BA(FR a1); BA(FR a2)], BR(FR res) =>
    OK [Pfmind res a1 a2]
  | "__builtin_fmax"%string, [BA(FR a1); BA(FR a2)], BR(FR res) =>
    OK [Pfmaxd res a1 a2]
  (* 64-bit integer arithmetic for a 32-bit platform *)
  | "__builtin_negl"%string, [BA_splitlong (BA (IR ah)) (BA (IR al))],
    BR_splitlong (BR (IR rh)) (BR (IR rl)) =>
    let conflict := if ireg_eq rl ah then true else false in
    OK (expand_int64_arith conflict rl
			(fun rl =>
                         [Psltuw X1 X0 (X al);
			 Psubw rl X0 (X al);
			 Psubw rh X0 (X ah);
			 Psubw rh (X rh) (X X1)]))
  | "__builtin_addl"%string, [BA_splitlong (BA (IR ah)) (BA (IR al));BA_splitlong (BA (IR bh)) (BA (IR bl))],
    BR_splitlong (BR (IR rh)) (BR (IR rl)) =>
    let conflict := if (ireg_eq rl bl) || (ireg_eq rl ah) || (ireg_eq rl bh) then true else false in
    OK (expand_int64_arith conflict rl
			(fun rl =>
			 [Paddw rl (X al) (X bl);
                         Psltuw X1 (X rl) (X bl);
			 Paddw rh (X ah) (X bh);
			 Paddw rh  (X rh) (X X1)]))
  | "__builtin_subl"%string, [BA_splitlong (BA (IR ah)) (BA (IR al));BA_splitlong (BA (IR bh)) (BA (IR bl))],
    BR_splitlong (BR (IR rh)) (BR (IR rl)) =>
    let conflict := if (ireg_eq rl ah) || (ireg_eq rl bh) then true else false in
    OK (expand_int64_arith conflict rl
			(fun rl =>
                         [Psltuw X1 (X al) (X bl);
			 Psubw rl (X al) (X bl);
			 Psubw rh (X ah) (X bh);
			 Psubw rh (X rh) (X X1)]))
  | "__builtin_mull"%string, [BA(IR a); BA(IR b)],
    BR_splitlong (BR (IR rh)) (BR (IR rl)) =>
    let conflict := if (ireg_eq rl a) || (ireg_eq rl b) then true else false in
     OK (expand_int64_arith conflict rl
                        (fun rl =>
                           [Pmulw rl (X a) (X b);
                           Pmulhuw rh (X a) (X b)]))
  | "__builtin_nop"%string, [], _ =>
     OK [Pnop]
  (* Catch-all *)
  | _,_,_ =>
     Error [MSG "unrecognized builtin "; MSG name]
  end.

Definition transf_instr f instr : res (list instruction) :=
  match instr with
  | Pbuiltin ef args res =>
    match ef with
    | EF_builtin name sg =>
      expand_builtin_inline f name args res
    | EF_vload chunk =>
      expand_builtin_vload chunk args res
    | EF_vstore chunk =>
      expand_builtin_vstore chunk args
    | EF_memcpy sz al =>
      expand_builtin_memcpy sz al args
    (* follow x86 *)
    | EF_annot_val kind txt targ =>
      OK [Pnop]
    | EF_annot _ _ _ =>
      OK [Pnop]
    | EF_debug _ _ _ =>
      Error [MSG "Unsupported Builtin Elimination: debug"]
    | EF_inline_asm _ _ _ =>
      Error [MSG "Unsupported Builtin Elimination: inline_asm"]
     | _ =>
       Error [MSG "Unsupported Builtin Elimination: unknown"]
    end
      
  (* we move some trivial instructions expansion here *)
  | Pseqw rd rs1 rs2 =>
    (* emulate based on the fact that x == 0 iff x <u 1 (unsigned cmp) *)
    if ireg0_eq rs2 X0 then
      OK [Psltiuw rd rs1 (Int.repr 1)]
    else
      OK [Pxorw rd rs1 rs2;Psltiuw rd (X rd) (Int.repr 1)]
  | Psnew rd rs1 rs2 =>
    (* emulate based on the fact that x != 0 iff 0 <u x (unsigned cmp) *)
    if ireg0_eq rs2 X0 then
      OK [Psltuw rd X0 rs1]
    else
      OK [Pxorw rd rs1 rs2;Psltuw rd X0 (X rd)]
  | Pseql rd rs1 rs2 =>
    (* emulate based on the fact that x == 0 iff x <u 1 (unsigned cmp) *)
    if ireg0_eq rs2 X0 then
      OK [Psltiul rd rs1 (Int64.repr 1)]
    else
      OK [Pxorl rd rs1 rs2;Psltiul rd (X rd) (Int64.repr 1)]
  | Psnel rd rs1 rs2 =>
    (* emulate based on the fact that x != 0 iff 0 <u x (unsigned cmp) *)
    if ireg0_eq rs2 X0 then
      OK [Psltul rd X0 rs1]
    else
      OK [Pxorl rd rs1 rs2;Psltul rd X0 (X rd)]
  | Pcvtl2w rd rs =>
    if Archi.ptr64 then
      OK [Paddiw rd rs (Int.zero)]
    else
      Error (msg"Pcvtl2w in 32bit mode")
  | Pcvtw2l r =>
    if Archi.ptr64 then
      OK []
    else
      Error (msg"Pcvtl2l in 32bit mode")
  | _ =>
    OK [instr]
  end.
             

Definition acc_transl_instr (f: function) (r:res code) (i:instruction) :=
  do acc_i <- r;
  do i' <- transf_instr f i;
  OK (acc_i ++ i').
  
Definition transl_code (f:function) (c:code) : res code :=
  do code <- fold_left (acc_transl_instr f) c (OK []);
  OK (code).


Definition transf_function (f: function) : res function :=
  do fn_code' <- transl_code f (fn_code f);
  OK {|
      fn_sig := fn_sig f;
      fn_code := fn_code';
      fn_stacksize := fn_stacksize f;
    |}.

Definition transf_fundef (f: Asm.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Asm.program) : res Asm.program :=
  transform_partial_program transf_fundef p.
    
         
