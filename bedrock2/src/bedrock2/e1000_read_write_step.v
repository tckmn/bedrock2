(*
Formalization of a subset of the functionality of Intel's 8254x Network Interface Cards.

PDF Spec:

PCI/PCI-X Family of Gigabit Ethernet Controllers Software Developer's Manual
82540EP/EM, 82541xx, 82544GC/EI, 82545GM/EM, 82546GB/EB, and 82547xx
https://www.intel.com/content/dam/doc/manual/pci-pci-x-family-gbe-controllers-software-dev-manual.pdf

These network cards were launched in the 2000s and discontinued in the 2010s, but continue to be a popular choice for virtualization, where they are often referred to as "e1000".
 *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require Import coqutil.Datatypes.HList coqutil.Byte.
Require Import coqutil.Z.BitOps.
Require coqutil.Map.SortedListZ.
Require Import coqutil.Datatypes.ZList.
Import ZList.List.ZIndexNotations. Local Open Scope zlist_scope.
Require Import coqutil.Datatypes.RecordSetters. Import DoubleBraceUpdate.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.StateMachineBasedExtSpec_wp.
Require Import bedrock2.WordNotations. Local Open Scope word_scope.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.SepLib.
Require Import bedrock2.SepBulletPoints. Local Open Scope sep_bullets_scope.
Require Import bedrock2.RecordPredicates.
Require Import bedrock2.TraceInspection.
Require Import bedrock2.memory_mapped_ext_spec.
Require Import bedrock2.e1000_state. (* for rx/tx_desc and separation logic definitions *)

(* Not part of the spec, but a convention we chose to hardcode here: *)
Definition E1000_REGS := 0x40000000.

(* Bitfields of Receive Control Register (Section 13.4.22) *)
Module RCTL.
  (* Bit 0 is reserved *)
  Definition EN := 1. (* Receiver Enable *)
  Definition SBP := 2. (* Store Bad Packets *)
  Definition UPE := 3. (* Unicast Promiscuous Enabled *)
  Definition MPE := 4. (* Multicast Promiscuous Enabled *)
  Definition LPE := 5. (* Long Packet Reception Enable *)
  Definition LBM_start := 6. (* Loopback mode *)
  Definition LBM_pastend := 8.
  Definition RDMTS_start := 8. (* Receive Descriptor Minimum Threshold Size *)
  Definition RDMTS_pastend := 10.
  (* Bits 10 and 11 are reserved *)
  Definition MO_start := 12. (* Multicast Offset *)
  Definition MO_pastend := 14.
  (* Bit 14 is reserved *)
  Definition BAM := 15. (* Broadcast Accept Mode. *)
  Definition BSIZE_start := 16. (* Receive Buffer Size *)
  (* If RCTL.BSEX = 0b: 00b =   2048 B, 01b =  1024 B, 10b =  512 B, 11b =  256 B.
     If RCTL.BSEX = 1b: 00b = Reserved, 01b = 16384 B, 10b = 8192 B, 11b = 4096 B. *)
  Definition BSIZE_pastend := 18.
  Definition VFE := 18. (* VLAN Filter Enable *)
  Definition CFIEN := 19. (* Canonical Form Indicator Enable *)
  Definition CFI := 20. (* Canonical Form Indicator bit value *)
  (* Bit 21 is reserved *)
  Definition DPF := 22.
  Definition PMCF := 23. (* Pass MAC Control Frames *)
  (* Bit 24 is reserved *)
  Definition BSEX := 25. (* Buffer Size Extension *)
  Definition SECRC := 26. (* Strip Ethernet CRC from incoming packet *)
  (* Bits 27 to 31 are reserved *)
End RCTL.

Section WithMem.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {mem: map.map word Byte.byte}.

  Local Notation IReg ofs init := (InitializedRegister (E1000_REGS + ofs) init)
    (only parsing).
  Local Notation UReg ofs := (UninitializedRegister (E1000_REGS + ofs))
    (only parsing).

  (* E1000 register offsets from Section 13.4 *)

  Definition E1000_RCTL := IReg 0x100 0. (* Receive Control Register *)

  Definition E1000_RDBAL := UReg 0x2800. (* base addr (lo 32 bits) of receive queue *)
  Definition E1000_RDBAH := UReg 0x2804. (* base addr (hi 32 bits) of receive queue *)
  Definition E1000_RDLEN := IReg 0x2808 0. (* length of receive queue in bytes *)
  Definition E1000_RDH := IReg 0x2810 0. (* receive queue head *)
  Definition E1000_RDT := IReg 0x2818 0. (* receive queue tail *)
  Definition E1000_TDBAL := UReg 0x3800. (* base addr (lo 32 bits) of transmit queue *)
  Definition E1000_TDBAH := UReg 0x3804. (* base addr (hi 32 bits) of transmit queue *)
  Definition E1000_TDLEN := IReg 0x3808 0. (* length of transmit queue in bytes *)
  Definition E1000_TDH := IReg 0x3810 0. (* transmit queue head *)
  Definition E1000_TDT := IReg 0x3818 0. (* transmit queue tail *)

  (* TODO some registers are safe to get using `get_rw_reg REG_NAME`, whereas others
     have "ignore on write" semantics and thus need a special get_rw_REGNAME.
     How can we enforce one never forgets to use the special getter if there is one? *)

  Definition getRDH(t: trace)(ret: Z): Prop :=
    exists r, get_rw_reg0 t (register_address E1000_RDH) = Some r /\ \[r] = ret.

  Definition getTDH(t: trace)(ret: Z): Prop :=
    exists r, get_rw_reg0 t (register_address E1000_TDH) = Some r /\ \[r] = ret.

  Definition getRDBAL(t: trace)(ret: word): Prop :=
    exists rdbal, get_rw_reg0 t (register_address E1000_RDBAL) = Some rdbal /\
    ret = /[Z.land (Z.lnot 0xf) \[rdbal]].

  Definition getRDBAH(t: trace)(ret: word): Prop. Admitted.

  Definition getRDBA(t: trace)(ret: word): Prop. Admitted. (*
    let/c rdbal := getRDBAL t in
    let/c rdbah := getRDBAH t in
    exists rdba, \[rdba] = \[rdbal] + \[rdbah] * 2^32 /\ ret rdba. *)

  Definition getTDBAL(t: trace)(ret: word): Prop. Admitted. (*
    let/c tdbal := getrw_reg E1000_TDBAL t in
    ret /[Z.land (Z.lnot 0xf) \[tdbal]].*)

  Definition getTDBAH(t: trace)(ret: word): Prop. Admitted.

  Definition getTDBA(t: trace)(ret: word): Prop. Admitted. (*
    let/c tdbal := getTDBAL t in
    let/c tdbah := getTDBAH t in
    exists tdba, \[tdba] = \[tdbal] + \[tdbah] * 2^32 /\ ret tdba. *)

  Definition get_receive_queue_cap(t: trace)(ret: Z): Prop. Admitted. (* :=
    let/c rdlen := getdescriptor_length E1000_RDLEN t in
    exists n, n * 16 = \[rdlen] /\ ret n.*)

  Definition get_transmit_queue_cap(t: trace)(ret: Z): Prop. Admitted. (*
    let/c tdlen := getdescriptor_length E1000_TDLEN t in
    exists n, n * 16 = \[tdlen] /\ ret n.*)

  (* Size of the receive buffers. If a packet doesn't fit, it is split into multiple
     buffers, using multiple descriptors.
     If RCTL.BSEX = 0b: 00b =   2048 B, 01b =  1024 B, 10b =  512 B, 11b =  256 B.
     If RCTL.BSEX = 1b: 00b = Reserved, 01b = 16384 B, 10b = 8192 B, 11b = 4096 B. *)
  Definition get_receive_buf_size(t: trace)(ret: Z): Prop :=
    exists rctl, get_rw_reg0 t (register_address E1000_RCTL) = Some rctl /\
    let bsex := Z.testbit \[rctl] RCTL.BSEX in
    let bsize := bitSlice \[rctl] RCTL.BSIZE_start RCTL.BSIZE_pastend in
    if bsex then
      match bsize with
      | 1 => ret = 16384
      | 2 => ret = 8192
      | 3 => ret = 4096
      | _ => False
      end
    else
      match bsize with
      | 0 => ret = 2048
      | 1 => ret = 1024
      | 2 => ret = 512
      | 3 => ret = 256
      | _ => False
      end.

  (* This are just the registers, and do not include the owned memory or the queues *)
  Record initialized_e1000_state := {
    rx_queue_base_addr: word; (* RDBAL/RDBAH, 64 bits total, but need to fit into a word *)
    tx_queue_base_addr: word; (* TDBAL/TDBAH, 64 bits total, but need to fit into a word *)
    rx_queue_cap: Z; (* RDLEN / 16 *)
    tx_queue_cap: Z; (* TDLEN / 16 *)
    (* Size of the receive buffers. If a packet doesn't fit, it is split into multiple
       buffers, using multiple descriptors.
       Hardware supports the following receive buffer sizes:
       256 B, 512 B, 1024 B, 2048 B, 4096 B, 8192 B, 16384 B (Section 3.2.2).
       The buffer size is controlled using RCTL.BSIZE and RCTL.BSEX (Section 13.4.22). *)
    rx_buf_size: Z;
    rx_queue_head: Z; (* RDH *)
    tx_queue_head: Z; (* TDH *)
  }.

  Definition e1000_initialized(s: initialized_e1000_state)(t: trace): Prop :=
    getRDBA t s.(rx_queue_base_addr) /\
    getTDBA t s.(tx_queue_base_addr) /\
    get_receive_queue_cap t s.(rx_queue_cap) /\
    get_transmit_queue_cap t s.(tx_queue_cap) /\
    get_receive_buf_size t s.(rx_buf_size) /\
    getRDH t s.(rx_queue_head) /\
    getTDH t s.(tx_queue_head).

  (* Potential notations for (circular_buffer_slice elem n i vs addr):
     * addr |-(->i, mod n)-> vs
     * addr [⇥i ⟳n]-> vs
     * addr [shift i, mod size]-> vs
     * vs @[+i, mod n] addr  *)

  Definition e1000_invariant(s: initialized_e1000_state)
    (rxq: list (rx_desc * buf))(txq: list (tx_desc * buf)): mem -> Prop :=
    <{ * circular_buffer_slice (rxq_elem s.(rx_buf_size))
           s.(rx_queue_cap) s.(rx_queue_head) rxq s.(rx_queue_base_addr)
       * circular_buffer_slice txq_elem
           s.(rx_queue_cap) s.(tx_queue_head) txq s.(tx_queue_base_addr) }>.

  Inductive e1000_read_step:
    forall (sz: nat), (* number of bytes to read *)
    trace -> (* trace of events that happened so far *)
    word -> (* address to be read *)
    (tuple byte sz -> mem -> Prop) -> (* postcondition on returned value and memory *)
    Prop :=
  (* new RDH can be anywhere between old RDH (incl) and old RDT (excl),
     we receive the memory chunk for each descriptor between old and new RDH,
     as well as the buffers pointed to by them, which contain newly received
     packets *)
  | read_RDH_step: forall t mNIC s rxq txq post,
      externally_owned_mem t mNIC ->
      e1000_initialized s t ->
      e1000_invariant s rxq txq mNIC ->
      (forall mRcv (done: list (rx_desc * buf)),
          len done <= len rxq ->
          List.map fst done = List.map fst rxq[:len done] ->
          (* snd (new buffer) can be any bytes *)
          circular_buffer_slice (rxq_elem s.(rx_buf_size))
            s.(rx_queue_cap) s.(rx_queue_head) done s.(rx_queue_base_addr) mRcv ->
          post (LittleEndian.split 4 ((s.(rx_queue_head) + len done) mod s.(rx_queue_cap))) mRcv) ->
      e1000_read_step 4 t (register_address E1000_RDH) post
  .

  Inductive e1000_write_step:
    forall (sz: nat), (* number of bytes to write *)
    trace -> (* trace of events that happened so far *)
    word -> (* address to be written *)
    tuple byte sz -> (* value to be written *)
    mem -> (* memory whose ownership is passed to the external world *)
    Prop := .

(* TODO what about 13.4.28 "Reading the descriptor head to determine which buffers are
   finished is not reliable" and 13.4.39 "Reading the transmit descriptor head to
   determine which buffers have been used (and can be returned to the memory pool)
   is not reliable".
   --> need to read DD field ("descriptor done") in RDESC.STATUS field and
       DD field in TDESC.STATUS field.
   3.3.3: The DD bit reflects status of all descriptors up to and including the one with
          the RS bit set (or RPS for the 82544GC/EI).
     (so software can decide to only set the RS (report status) bit for certain
      descriptors and only check the DD bit of those)
   So the status field needs to be written by the NIC and concurrently be read by software,
   so we can't strictly assign this piece of memory to either NIC or software! *)

  Global Instance e1000_MemoryMappedExtCalls: MemoryMappedExtCalls := {
    read_step := e1000_read_step;
    write_step := e1000_write_step;
  }.

  Global Instance e1000_MemoryMappedExtCallsOk: MemoryMappedExtCallsOk e1000_MemoryMappedExtCalls.
  Proof.
  Admitted.

  Local Open Scope string_scope.

  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Context {locals: map.map String.string word}.

  (* TODO move to bedrock2.Semantics *)
  Lemma exec_interact_cps{ext_spec: ExtSpec}:
    forall e binds action arges args t m l post mKeep mGive,
      map.split m mKeep mGive ->
      eval_call_args m l arges = Some args ->
      ext_spec t mGive action args (fun mReceive resvals =>
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (cons ((mGive, action, args), (mReceive, resvals)) t) m' l') ->
      exec e (cmd.interact binds action arges) t m l post.
  Proof. intros. eauto using exec.interact. Qed.

  Local Open Scope string_scope.

  (* read RDH: new RDH can be anywhere between old RDH (incl) and old RDT (excl),
     we receive the memory chunk for each descriptor between old and new RDH,
     as well as the buffers pointed to by them, which contain newly received packets
  Lemma wp_read_RDH: forall e mNIC rdh tdh old_rx_descs rx_queue_cap tx_queue_cap
                            rdba tdba rx_buf_size t m l r post
                            rxq txq rx_bufs tx_bufs,
      externally_owned_mem t mNIC ->
      (* begin NIC invariant, TODO factor out *)
      getRDBA t rdba ->
      getRDH t rdh ->
      get_receive_queue_cap t rx_queue_cap ->
      get_receive_buf_size t rx_buf_size ->
      getTDBA t tdba ->
      getTDH t tdh ->
      get_transmit_queue_cap t tx_queue_cap ->
      let rx_buf_addrs := List.map (fun d => /[d.(rx_desc_addr)]) rxq in
      let tx_buf_addrs := List.map (fun d => /[d.(tx_desc_addr)]) txq in
      <{ (* receive-related: *)
          * circular_buffer_slice rx_desc_t rx_queue_cap \[rdh] rxq rdba
          * scattered_array (array (uint 8) rx_buf_size) rx_bufs rx_buf_addrs
          (* transmit-related: *)
          * circular_buffer_slice tx_desc_t tx_queue_cap \[tdh] txq tdba
          * layout_absolute (List.map (fun pkt => array' (uint 8) pkt) tx_bufs) tx_buf_addrs
        }> mNIC ->
      (* end of NIC invariant *)
      (forall (m' mRcv: mem) (packets: list buf),
          map.split m' mRcv m ->
          len packets <= len rxq ->
          let new_RDH := /[(\[rdh] + len packets) mod rx_queue_cap] in
          (* we get back a (wrapping) slice of the rx queue as well as the corresponding
             buffers *)
          <{ * circular_buffer_slice rx_desc_t rx_queue_cap \[rdh]
                                     old_rx_descs[:len packets] rdba
             * scattered_array (array (uint 8) rx_buf_size) packets
                   (List.map (fun d => /[d.(rx_desc_addr)]) (old_rx_descs[:len packets]))
          }> mRcv ->
          post (cons ((map.empty, "MMIOREAD", [| register_address E1000_RDH |]),
                      (mRcv, [|new_RDH|])) t)
               m' (map.put l r new_RDH)) ->
      exec e (cmd.interact [|r|] "MMIOREAD" [|expr.literal \[register_address E1000_RDH]|])
           t m l post.
  Proof.
    intros.
    eapply exec_interact_cps.
    2: {
      cbn [eval_call_args eval_expr]. rewrite word.of_Z_unsigned. reflexivity.
    }
    2: {
      unfold ext_spec. left. do 2 (split; [reflexivity | ]).
      eexists. split. 1: reflexivity.
      (* looks promising, but still need to determine ?mGive and ?mKeep *)
  Abort. *)

End WithMem.
