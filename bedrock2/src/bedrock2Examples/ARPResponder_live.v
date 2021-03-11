Require Import Coq.derive.Derive.
Require Import coqutil.Z.Lia.
Require coqutil.Word.BigEndian.
Require Import coqutil.Byte coqutil.Datatypes.HList.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Tactics.letexists coqutil.Tactics.Tactics coqutil.Tactics.rewr coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.rewr.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.NotationsCustomEntry coqutil.Z.HexNotation.
Require Import bedrock2.FE310CSemantics.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Array.
Require Import bedrock2.ZnWords.
Require Import bedrock2.ptsto_bytes bedrock2.Scalars.
Require Import bedrock2.WeakestPrecondition bedrock2.ProgramLogic.
Require Import bedrock2.ZnWords.
Require Import coqutil.Word.SimplWordExpr.
Require Import bedrock2.footpr.

(* TODO put into coqutil and also use in lightbulb.v *)
Module word. Section WithWord.
  Import ZArith.
  Local Open Scope Z_scope.
  Context {width} {word: word.word width} {ok : word.ok word}.
  Lemma unsigned_of_Z_nowrap x:
    0 <= x < 2 ^ width -> word.unsigned (word.of_Z x) = x.
  Proof.
    intros. rewrite word.unsigned_of_Z. unfold word.wrap. rewrite Z.mod_small; trivial.
  Qed.
  Lemma of_Z_inj_small{x y}:
    word.of_Z x = word.of_Z y -> 0 <= x < 2 ^ width -> 0 <= y < 2 ^ width -> x = y.
  Proof.
    intros. apply (f_equal word.unsigned) in H. rewrite ?word.unsigned_of_Z in H.
    unfold word.wrap in H. rewrite ?Z.mod_small in H by assumption. assumption.
  Qed.

  Lemma and_bool_to_word: forall (b1 b2: bool),
    word.and (if b1 then word.of_Z 1 else word.of_Z 0)
             (if b2 then word.of_Z 1 else word.of_Z 0) =
    if (andb b1 b2) then word.of_Z 1 else word.of_Z 0.
  Proof.
    assert (1 < 2 ^ width). {
      pose proof word.width_pos.
      change 1 with (2 ^ 0). apply Z.pow_lt_mono_r; blia.
    }
    destruct b1; destruct b2; simpl; apply word.unsigned_inj; rewrite word.unsigned_and;
      unfold word.wrap; rewrite ?unsigned_of_Z_nowrap by blia;
        rewrite ?Z.land_diag, ?Z.land_0_r, ?Z.land_0_l;
        apply Z.mod_small; blia.
  Qed.
End WithWord. End word.

Module List.
  Import List.ListNotations. Open Scope list_scope.
  Section MapWithIndex.
    Context {A B: Type} (f: A -> nat -> B).
    Fixpoint map_with_start_index(start: nat)(l: list A): list B :=
      match l with
      | nil => nil
      | h :: t => f h start :: map_with_start_index (S start) t
      end.
    Definition map_with_index: list A -> list B := map_with_start_index O.

    Lemma map_with_start_index_app: forall l l' start,
        map_with_start_index start (l ++ l') =
        map_with_start_index start l ++ map_with_start_index (start + List.length l) l'.
    Proof.
      induction l; intros.
      - simpl. rewrite PeanoNat.Nat.add_0_r. reflexivity.
      - simpl. f_equal. rewrite IHl. f_equal. f_equal. Lia.lia.
    Qed.

    Lemma map_with_index_app: forall l l',
        map_with_index (l ++ l') = map_with_index l ++ map_with_start_index (List.length l) l'.
    Proof. intros. apply map_with_start_index_app. Qed.

    Lemma map_with_start_index_cons: forall a l start,
        map_with_start_index start (a :: l) = f a start :: map_with_start_index (S start) l.
    Proof. intros. reflexivity. Qed.

    Lemma map_with_index_cons: forall a l,
        map_with_index (a :: l) = f a 0 :: map_with_start_index 1 l.
    Proof. intros. reflexivity. Qed.

    Lemma skipn_map_with_start_index: forall i start l,
        skipn i (map_with_start_index start l) = map_with_start_index (start + i) (skipn i l).
    Proof.
      induction i; intros.
      - simpl. rewrite PeanoNat.Nat.add_0_r. reflexivity.
      - destruct l; simpl. 1: reflexivity. rewrite IHi. f_equal. Lia.lia.
    Qed.

    Lemma map_with_start_index_nth_error: forall (n start: nat) (l: list A) d,
        List.nth_error l n = Some d ->
        List.nth_error (map_with_start_index start l) n = Some (f d (start + n)).
    Proof.
      induction n; intros.
      - destruct l; simpl in *. 1: discriminate. rewrite PeanoNat.Nat.add_0_r. congruence.
      - destruct l; simpl in *. 1: discriminate. erewrite IHn. 2: eassumption. f_equal. f_equal. Lia.lia.
    Qed.

    Lemma map_with_index_nth_error: forall (n: nat) (l : list A) d,
        List.nth_error l n = Some d ->
        List.nth_error (map_with_index l) n = Some (f d n).
    Proof. intros. eapply map_with_start_index_nth_error. assumption. Qed.

  End MapWithIndex.

  Section WithA.
    Context {A: Type}.

    Lemma nth_error_to_hd_skipn: forall n (l: list A) a d,
        List.nth_error l n = Some a ->
        hd d (skipn n l) = a.
    Proof.
      induction n; intros.
      - destruct l; simpl in *. 1: discriminate. congruence.
      - destruct l; simpl in *. 1: discriminate. eauto.
    Qed.

    Definition generate(len: nat)(f: nat -> A): list A := List.map f (List.seq 0 len).
  End WithA.
End List.

Definition TODO{T: Type}: T. Admitted.

Infix "^+" := word.add  (at level 50, left associativity).
Infix "^-" := word.sub  (at level 50, left associativity).
Infix "^*" := word.mul  (at level 40, left associativity).
Infix "^<<" := word.slu  (at level 37, left associativity).
Infix "^>>" := word.sru  (at level 37, left associativity).
Notation "/[ x ]" := (word.of_Z x)       (* squeeze a Z into a word (beat it with a / to make it smaller) *)
  (format "/[ x ]").
Notation "\[ x ]" := (word.unsigned x)   (* \ is the open (removed) lid of the modulo box imposed by words, *)
  (format "\[ x ]").                     (* let a word fly into the large Z space *)

Section WithParameters.
  Context {p : FE310CSemantics.parameters}.
  Import Syntax BinInt String List.ListNotations ZArith.
  Local Set Implicit Arguments.
  Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
  Local Coercion expr.literal : Z >-> expr.
  Local Coercion expr.var : String.string >-> expr.
  Coercion Z.of_nat : nat >-> Z.
  Coercion byte.unsigned : byte >-> Z.
  Notation len := List.length.
  Notation "'bytetuple' sz" := (HList.tuple byte (@Memory.bytes_per width sz)) (at level 10).

  Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).

  (* TODO move (to Scalars.v?) *)
  Lemma load_bounded_Z_of_sep: forall sz addr (value: Z) R m,
      0 <= value < 2 ^ (Z.of_nat (bytes_per (width:=width) sz) * 8) ->
      sep (truncated_scalar sz addr value) R m ->
      Memory.load_Z sz m addr = Some value.
  Proof.
    intros.
    cbv [load scalar littleendian load_Z] in *.
    erewrite load_bytes_of_sep. 2: exact H0.
    apply f_equal.
    rewrite LittleEndian.combine_split.
    apply Z.mod_small.
    assumption.
  Qed.

  Lemma load_of_sep_truncated_scalar: forall sz addr (value: Z) R m,
      0 <= value < 2 ^ (Z.of_nat (bytes_per (width:=width) sz) * 8) ->
      sep (truncated_scalar sz addr value) R m ->
      Memory.load sz m addr = Some (word.of_Z value).
  Proof.
    intros. unfold Memory.load.
    erewrite load_bounded_Z_of_sep by eassumption.
    reflexivity.
  Qed.

  Definition BEBytesToWord{n: nat}(bs: tuple byte n): word := word.of_Z (BigEndian.combine n bs).

  Definition ZToBEWord(n: nat)(x: Z): word := BEBytesToWord (BigEndian.split n x).

  Definition byteToWord(b: byte): word := word.of_Z (byte.unsigned b).

  (* An n-byte unsigned little-endian number v at address a.
     Enforces that v fits into n bytes. *)
  Definition LEUnsigned(n: nat)(addr: word)(v: Z)(m: mem): Prop :=
    exists bs: tuple byte n, ptsto_bytes n addr bs m /\ v = LittleEndian.combine n bs.

  (* Enforces that v fits into (bytes_per sz) bytes.
     To be used as the one and only base-case separation logic assertion, because using
     load1/2/4/8 will convert the value it puts into the dst register to word anyways,
     so it makes sense to hardcode the type of v to be word. *)
  Definition value(sz: access_size)(addr v: word): mem -> Prop :=
    LEUnsigned (bytes_per (width:=width) sz) addr (word.unsigned v).

  Lemma load_of_sep_value: forall sz addr v R m,
      sep (value sz addr v) R m ->
      Memory.load sz m addr = Some v.
  Proof.
    unfold value, Memory.load, Memory.load_Z, LEUnsigned. intros.
    assert (exists bs : tuple Init.Byte.byte (bytes_per sz),
               sep (ptsto_bytes (bytes_per sz) addr bs) R m /\
               word.unsigned v = LittleEndian.combine (bytes_per (width:=width) sz) bs) as A. {
      unfold sep in *.
      decompose [ex and] H.
      eauto 10.
    }
    clear H. destruct A as (bs & A & E).
    erewrite load_bytes_of_sep by eassumption.
    rewrite <- E.
    rewrite word.of_Z_unsigned.
    reflexivity.
  Qed.

  Inductive TypeSpec: Type -> Type :=
  | TByte: TypeSpec byte
  | TStruct{R: Type}(fields: list (FieldSpec R)): TypeSpec R
  (* dynamic number of elements: *)
  | TArray{E: Type}(elemSize: Z)(elemSpec: TypeSpec E): TypeSpec (list E)
  (* number of elements statically known: *)
  | TTuple{E: Type}(count: nat)(elemSize: Z)(elemSpec: TypeSpec E): TypeSpec (tuple E count)
  with FieldSpec: Type -> Type :=
  | FField{R F: Type}(getter: R -> F)(setter: R -> F -> R)(fieldSpec: TypeSpec F)
    : FieldSpec R.

  Fixpoint TypeSpec_size{R: Type}(sp: TypeSpec R): R -> Z :=
    match sp with
    | TByte => fun r => 1
    | TStruct fields => fun r => List.fold_right (fun f res => FieldSpec_size f r + res) 0 fields
    | TArray elemSize _ => fun l => List.length l * elemSize
    | TTuple n elemSize _ => fun t => n * elemSize
    end
  with FieldSpec_size{R: Type}(f: FieldSpec R): R -> Z :=
    match f with
    | FField getter setter sp => fun r => TypeSpec_size sp (getter r)
    end.

  (* sum of the sizes of the first i fields *)
  Definition offset{R: Type}(r: R)(fields: list (FieldSpec R))(i: nat): Z :=
    List.fold_right (fun f res => FieldSpec_size f r + res) 0 (List.firstn i fields).

  Section dataAt_recursion_helpers.
    Context (dataAt: forall {R: Type}, TypeSpec R -> word -> R -> mem -> Prop).

    Definition fieldAt{R: Type}(f: FieldSpec R)(i: nat): list (FieldSpec R) -> word -> R -> mem -> Prop :=
      match f with
      | FField getter setter sp => fun fields base r => dataAt sp (base ^+ /[offset r fields i]) (getter r)
      end.

    Definition fieldsAt{R: Type}(fields: list (FieldSpec R))(start: word)(r: R): list (mem -> Prop) :=
      List.map_with_index (fun f i => fieldAt f i fields start r) fields.

    Definition arrayAt{E: Type}(elemSize: Z)(elem: TypeSpec E)(start: word): list E -> list (mem -> Prop) :=
      List.map_with_index (fun e i => dataAt elem (start ^+ /[i * elemSize]) e).
  End dataAt_recursion_helpers.

  Fixpoint dataAt{R: Type}(sp: TypeSpec R){struct sp}: word -> R -> mem -> Prop :=
    match sp with
    | TByte => ptsto
    | @TStruct R fields => fun base r => seps (fieldsAt (@dataAt) fields base r)
    | @TArray E elemSize elem => fun base l => seps (arrayAt (@dataAt) elemSize elem base l)
    | @TTuple E n elemSize elem => fun base t => seps (arrayAt (@dataAt) elemSize elem base (tuple.to_list t))
    end.

  (* ** Packet Formats *)

  Definition EtherTypeARP := tuple.of_list [Byte.x08; Byte.x06].
  Definition EtherTypeIPv4 := tuple.of_list [Byte.x08; Byte.x00].

  Definition ETHERTYPE_IPV4_LE: Z :=
    Eval compute in (LittleEndian.combine 2 EtherTypeIPv4).

  Definition ETHERTYPE_ARP_LE: Z :=
    Eval compute in (LittleEndian.combine 2 EtherTypeARP).

(*  Definition MAC := tuple byte 6.*)

  Definition IPv4 := tuple byte 4.

  Record EthernetPacket(Payload: Type) := mkEthernetARPPacket {
    dstMAC: tuple byte 6;
    srcMAC: tuple byte 6;
    etherType: tuple byte 2; (* <-- must initially accept all possible two-byte values *)
    payload: Payload;
  }.

  Definition EthernetPacket_spec{Payload: Type}(Payload_spec: TypeSpec Payload) := TStruct [
    FField (@dstMAC Payload) TODO (TTuple 6 1 TByte);
    FField (@srcMAC Payload) TODO (TTuple 6 1 TByte);
    FField (@etherType Payload) TODO (TTuple 2 1 TByte);
    FField (@payload Payload) TODO Payload_spec
  ].

  Record ARPPacket := mkARPPacket {
    htype: tuple byte 2; (* hardware type *)
    ptype: tuple byte 2; (* protocol type *)
    hlen: byte;          (* hardware address length (6 for MAC addresses) *)
    plen: byte;          (* protocol address length (4 for IPv4 addresses) *)
    oper: tuple byte 2;
    sha: tuple byte 6;  (* sender hardware address *)
    spa: IPv4; (* sender protocol address *)
    tha: tuple byte 6;  (* target hardware address *)
    tpa: IPv4; (* target protocol address *)
  }.

  Definition ARPPacket_spec: TypeSpec ARPPacket := TStruct [
    FField htype TODO (TTuple 2 1 TByte);
    FField ptype TODO (TTuple 2 1 TByte);
    FField hlen TODO TByte;
    FField plen TODO TByte;
    FField oper TODO (TTuple 2 1 TByte);
    FField sha TODO (TTuple 6 1 TByte);
    FField spa TODO (TTuple 4 1 TByte);
    FField tha TODO (TTuple 6 1 TByte);
    FField tpa TODO (TTuple 4 1 TByte)
  ].

  Definition HTYPE := tuple.of_list [Byte.x00; Byte.x01].
  Definition PTYPE := tuple.of_list [Byte.x80; Byte.x00].
  Definition HLEN := Byte.x06.
  Definition PLEN := Byte.x04.
  Definition OPER_REQUEST := tuple.of_list [Byte.x00; Byte.x01].
  Definition OPER_REPLY := tuple.of_list [Byte.x00; Byte.x02].

  Definition HTYPE_LE := Ox"0100".
  Definition PTYPE_LE := Ox"0080".

  Definition validPacket(pk: EthernetPacket ARPPacket): Prop :=
    (pk.(etherType) = EtherTypeARP \/ pk.(etherType) = EtherTypeIPv4) /\
    pk.(payload).(htype) = HTYPE /\
    pk.(payload).(ptype) = PTYPE /\
    pk.(payload).(hlen) = HLEN /\
    pk.(payload).(plen) = PLEN /\
    (pk.(payload).(oper) = OPER_REQUEST \/ pk.(payload).(oper) = OPER_REPLY).

  Record ARPConfig := mkARPConfig {
    myMAC: tuple byte 6;
    myIPv4: IPv4;
  }.

  Context (cfg: ARPConfig).

  Definition needsARPReply(req: EthernetPacket ARPPacket): Prop :=
    req.(etherType) = EtherTypeARP /\
    req.(payload).(oper) = OPER_REQUEST /\
    req.(payload).(tpa) = cfg.(myIPv4). (* <-- we only reply to requests asking for our own MAC *)

  Definition ARPReply(req: EthernetPacket ARPPacket): EthernetPacket ARPPacket :=
    {| dstMAC := req.(payload).(sha);
       srcMAC := cfg.(myMAC);
       etherType := EtherTypeARP;
       payload := {|
         htype := HTYPE;
         ptype := PTYPE;
         hlen := HLEN;
         plen := PLEN;
         oper := OPER_REPLY;
         sha := cfg.(myMAC); (* <-- the actual reply *)
         spa := cfg.(myIPv4);
         tha := req.(payload).(sha);
         tpa := req.(payload).(spa)
       |}
    |}.

  Lemma bytesToARPPacket: forall a bs,
      28 = len bs ->
      exists p: ARPPacket,
        iff1 (array ptsto /[1] a bs) (dataAt ARPPacket_spec a p).
  Proof.
    intros.
    eexists {| oper := _ |}. cbn -[tuple.to_list].

  Admitted.

  Lemma bytesToEthernetARPPacket: forall a bs,
      64 = len bs ->
      exists p: EthernetPacket ARPPacket,
        iff1 (array ptsto /[1] a bs) (dataAt (EthernetPacket_spec ARPPacket_spec) a p).
  Proof.
    intros.
    eexists {| payload := _ |}. cbn -[tuple.to_list].

    (* TODO messy *)
  Admitted.

  Definition addr_in_range(a start: word)(len: Z): Prop :=
    word.unsigned (word.sub a start) <= len.

  Definition subrange(start1: word)(len1: Z)(start2: word)(len2: Z): Prop :=
    0 <= len1 <= len2 /\ addr_in_range start1 start2 (len2-len1).

  Notation "a ,+ m 'c=' b ,+ n" := (subrange a m b n)
    (no associativity, at level 10, m at level 1, b at level 1, n at level 1,
     format "a ,+ m  'c='  b ,+ n").

  Record dummy_packet := {
    dummy_src: tuple byte 4;
 (* if we want dependent field types (instead of just dependent field lengths), we also need
    to figure out how to set/update such fields...
    dummy_dst_kind: bool;
    dummy_dst: if dummy_dst_kind then tuple byte 4 else tuple byte 6;
    *)
    dummy_dst: tuple byte 4;
    dummy_len: tuple byte 2;
    dummy_data: list byte;
    dummy_padding: list byte (* non-constant offset *)
  }.

  Definition set_dummy_src d x :=
    Build_dummy_packet x (dummy_dst d) (dummy_len d) (dummy_data d) (dummy_padding d).
  Definition set_dummy_dst d x :=
    Build_dummy_packet (dummy_src d) x (dummy_len d) (dummy_data d) (dummy_padding d).
  Definition set_dummy_len d x :=
    Build_dummy_packet (dummy_src d) (dummy_dst d) x (dummy_data d) (dummy_padding d).
  Definition set_dummy_data d x :=
    Build_dummy_packet (dummy_src d) (dummy_dst d) (dummy_len d) x (dummy_padding d).
  Definition set_dummy_padding d x :=
    Build_dummy_packet (dummy_src d) (dummy_dst d) (dummy_len d) (dummy_data d) x.

  Definition dummy_spec: TypeSpec dummy_packet := TStruct [
    FField dummy_src set_dummy_src (TTuple 4 1 TByte);
    FField dummy_dst set_dummy_dst (TTuple 4 1 TByte);
    FField dummy_len set_dummy_len (TTuple 2 1 TByte);
    FField dummy_data set_dummy_data (TArray 1 TByte);
    FField dummy_padding set_dummy_padding (TArray 1 TByte)
  ].

  Record foo := {
    foo_count: tuple byte 4;
    foo_packet: dummy_packet;
    foo_packets: list dummy_packet;
  }.
  Definition set_foo_count f x :=
    Build_foo x (foo_packet f) (foo_packets f).
  Definition set_foo_packet f x :=
    Build_foo (foo_count f) x (foo_packets f).
  Definition set_foo_packets f x :=
    Build_foo (foo_count f) (foo_packet f) x.

  Definition foo_spec: TypeSpec foo := TStruct [
    FField foo_count set_foo_count (TTuple 4 1 TByte);
    FField foo_packet set_foo_packet dummy_spec;
    FField foo_packets set_foo_packets (TArray 256 dummy_spec)
  ].

  (* append-at-front direction (for constructing a path using backwards reasoning) *)
  Inductive lookup_path:
    (* input: start type, end type, *)
    forall {R F: Type},
    (* type spec, base address, and whole value found at empty path *)
    TypeSpec R -> word -> R ->
    (* output: type spec, address and value found at given path *)
    TypeSpec F -> word -> F -> Prop :=
  | lookup_path_Nil: forall R R' (sp: TypeSpec R) (sp': TypeSpec R') addr addr' r r',
      dataAt sp addr r = dataAt sp' addr' r' ->
      lookup_path sp addr r
                  sp' addr' r'
  | lookup_path_Field: forall R F R' (getter: R -> F) setter fields i sp sp' addr addr' (r: R) (r': R'),
      List.nth_error fields i = Some (FField getter setter sp) ->
      lookup_path sp (addr ^+ /[offset r fields i]) (getter r)
                  sp' addr' r' ->
      lookup_path (TStruct fields) addr r
                  sp' addr' r'
  | lookup_path_Index: forall R E (sp: TypeSpec R) r' len i (sp': TypeSpec E) l e addr addr',
      List.nth_error l i = Some e ->
      lookup_path sp (addr ^+ /[i * len]) e
                  sp' addr' r' ->
      lookup_path (TArray len sp) addr l
                  sp' addr' r'.

  Ltac assert_lookup_range_feasible :=
    match goal with
    | |- lookup_path ?sp ?addr ?v ?sp' ?addr' ?v' =>
      let range_start := eval cbn -[Z.add] in addr in
      let range_size := eval cbn -[Z.add] in (TypeSpec_size sp v) in
      let target_start := addr' in
      let target_size := eval cbn -[Z.add] in (TypeSpec_size sp' v') in
      assert (target_start,+target_size c= range_start,+range_size)
    end.

  Ltac check_lookup_range_feasible :=
    assert_succeeds (assert_lookup_range_feasible; [solve [unfold subrange, addr_in_range; ZnWords]|]).

  Goal forall base f R m,
      seps [dataAt foo_spec base f; R] m ->
      exists v,
        lookup_path foo_spec base f
                    (TTuple 2 1 TByte) (base ^+ /[12]) v.
  Proof.
    intros.

    Check f.(foo_packet).(dummy_len).
    eexists.

    (*Eval simpl in (path_value (PField (PField (PNil _) foo_packet) dummy_len) f).*)

    (* t = load2(base ^+ /[4] ^+ /[8])
       The range `(base+12),+2` corresponds to the field `f.(foo_packet).(dummy_len)`.
       Goal: use lia to find this path. *)
    set (target_start := (base ^+ /[12])).
    set (target_size := 2%Z).

    (* backward reasoning: *)

    (* check that path is still good *)
    match goal with
    | |- lookup_path ?sp ?addr ?v _ _ _ =>
      pose (range_start := addr); cbn -[Z.add] in range_start;
      pose (range_size := (TypeSpec_size sp v)); cbn -[Z.add] in range_size
    end.
    assert (target_start,+target_size c= range_start,+range_size) as T. {
      unfold subrange, addr_in_range. ZnWords.
    }
    clear range_start range_size T.

    eapply lookup_path_Field with (i := 1%nat); [reflexivity|]. (* <-- i picked by backtracking *)
    cbn.

    (* check that path is still good *)
    check_lookup_range_feasible.

    eapply lookup_path_Field with (i := 2%nat); [reflexivity|]. (* <-- i picked by backtracking *)
    cbn.

    (* check that path is still good *)
    check_lookup_range_feasible.

    eapply lookup_path_Nil.
    f_equal.

  try eapply word.unsigned_inj;
  lazymatch goal with
  | |- ?G => is_lia_prop G
  end.
  cleanup_for_ZModArith.
  simpl_list_length_exprs.
  unfold_Z_nat_consts.
  (* PARAMRECORDS *)
  simpl.
  canonicalize_word_width_and_instance.
  repeat wordOps_to_ZModArith_step.
  dewordify;
  clear_unused_nonProps.
  better_lia.
  Qed.

  (* ** Program logic rules *)

  (* We have two rules for conditionals depending on whether there are more commands afterwards *)

  Lemma if_split: forall e c b thn els t m l mc post,
      dexpr m l c b ->
      (word.unsigned b <> 0 -> exec e thn t m l mc post) ->
      (word.unsigned b =  0 -> exec e els t m l mc post) ->
    exec e (cmd.cond c thn els) t m l mc post.
  Admitted.

  Lemma if_merge: forall e t m l mc c thn els rest b Q1 Q2 post,
      dexpr m l c b ->
      (word.unsigned b <> 0 -> exec e thn t m l mc Q1) ->
      (word.unsigned b = 0  -> exec e els t m l mc Q2) ->
      (forall t' m' l' mc', word.unsigned b <> 0 /\ Q1 t' m' l' mc' \/
                            word.unsigned b = 0  /\ Q2 t' m' l' mc' ->
                            exec e rest t' m' l' mc' post) ->
      exec e (cmd.seq (cmd.cond c thn els) rest) t m l mc post.
  Admitted.

  Lemma assignment: forall e x a t m l mc rest post,
      WeakestPrecondition.expr m l a
        (fun v => forall mc, exec e rest t m (map.put l x v) mc post) ->
      exec e (cmd.seq (cmd.set x a) rest) t m l mc post.
  Admitted.

  Implicit Type post: trace -> mem -> locals -> MetricLogging.MetricLog -> Prop.

  Lemma seps_nth_error_to_head: forall i Ps P,
      List.nth_error Ps i = Some P ->
      iff1 (seps Ps) (sep P (seps (app (firstn i Ps) (tl (skipn i Ps))))).
  Proof.
    intros.
    etransitivity.
    - symmetry. eapply seps_nth_to_head.
    - eapply List.nth_error_to_hd_skipn in H. rewrite H. reflexivity.
  Qed.

  Lemma expose_lookup_path: forall R F sp base (r: R) sp' addr (v: F),
      lookup_path sp base r sp' addr v ->
      exists Frame, iff1 (dataAt sp base r) (sep (dataAt sp' addr v) Frame).
  Proof.
    induction 1.
    - subst. exists (emp True). rewrite H. cancel.
    - destruct IHlookup_path as [Frame IH]. simpl in IH.
      eexists.
      cbn.
      unfold fieldsAt at 1.
      eapply List.map_with_index_nth_error in H.
      rewrite seps_nth_error_to_head. 2: exact H.
      unfold fieldAt at 1.
      rewrite IH.
      ecancel.
    - destruct IHlookup_path as [Frame IH]. simpl in IH.
      eexists.
      cbn.
      unfold arrayAt at 1.
      eapply List.map_with_index_nth_error in H.
      rewrite seps_nth_error_to_head. 2: exact H.
      rewrite IH.
      ecancel.
  Qed.

  Lemma load_field0: forall sz m addr M i R sp (r: R) base (v: bytetuple sz),
      seps M m ->
      List.nth_error M i = Some (dataAt sp base r) ->
      lookup_path sp base r (TTuple _ 1 TByte) addr v ->
      Memory.load_bytes (bytes_per sz) m addr = Some v.
  Proof.
    intros.
    destruct (expose_lookup_path H1) as (Frame & P).
    cbn in P.
    simpl in P.
    eapply seps_nth_error_to_head in H0.
    eapply H0 in H.
    seprewrite_in P H.
    eapply load_bytes_of_sep.
    replace (ptsto_bytes (bytes_per sz) addr v) with (seps (arrayAt (@dataAt) 1 TByte addr (tuple.to_list v)))
      by exact TODO.
    simpl. (* PARAMRECORDS *)
    ecancel_assumption.
  Qed.

  Lemma load_field: forall sz m addr M i R sp (r: R) base v,
      seps M m ->
      List.nth_error M i = Some (dataAt sp base r) ->
      lookup_path sp base r (TTuple _ 1 TByte) addr v ->
      Memory.load sz m addr = Some /[LittleEndian.combine (bytes_per (width:=width) sz) v].
  Proof.
    intros.
    unfold Memory.load, Memory.load_Z.
    erewrite load_field0; eauto.
  Qed.

  (* optimized for easy backtracking *)
  Lemma load_field': forall sz m addr M R sp (r: R) base v,
      seps M m ->
      (exists i,
          List.nth_error M i = Some (dataAt sp base r) /\
          lookup_path sp base r (TTuple _ 1 TByte) addr v) ->
      Memory.load sz m addr = Some /[LittleEndian.combine (bytes_per (width:=width) sz) v].
  Proof.
    intros. destruct H0 as (i & ? & ?). eauto using load_field.
  Qed.

  Lemma load_field'': forall sz m addr R sp (r: R) base v (post: word -> Prop),
      (exists M,
        seps M m /\
        exists i,
          List.nth_error M i = Some (dataAt sp base r) /\
          lookup_path sp base r (TTuple _ 1 TByte) addr v /\
          post /[LittleEndian.combine (bytes_per (width:=width) sz) v]) ->
      WeakestPrecondition.load sz m addr post.
  Proof.
    intros. unfold WeakestPrecondition.load. firstorder eauto using load_field.
  Qed.

  Lemma tuple_byte_1: forall addr v,
      dataAt TByte addr v = dataAt (TTuple 1 1 TByte) addr (tuple.of_list [v]).
  Proof. intros. simpl. f_equal. ZnWords. Qed.

  Definition vc_func e '(innames, outnames, body) (t: trace) (m: mem) (argvs: list word)
                     (post : trace -> mem -> list word -> Prop) :=
    exists l, map.of_list_zip innames argvs = Some l /\ forall mc,
      exec e body t m l mc (fun t' m' l' mc' =>
        list_map (WeakestPrecondition.get l') outnames (fun retvs => post t' m' retvs)).

(* backtrackingly tries all nats strictly smaller than n *)
Ltac pick_nat n :=
  multimatch n with
  | S ?m => constr:(m)
  | S ?m => pick_nat m
  end.

  Definition nFields{A: Type}(sp: TypeSpec A): option nat :=
    match sp with
    | TStruct fields => Some (List.length fields)
    | _ => None
    end.

  Ltac lookup_field_step := once (
    let n := lazymatch goal with
    | |- lookup_path ?sp ?base ?r _ _ _ =>
      let l := eval cbv in (nFields sp) in
      lazymatch l with
      | Some ?n => n
      end
    end in
    let j := pick_nat n in
    eapply lookup_path_Field with (i := j); [reflexivity|]; cbn;
    check_lookup_range_feasible).

  Ltac lookup_done :=
    eapply lookup_path_Nil; first [ apply tuple_byte_1 | f_equal; ZnWords ].

Ltac cleanup_step :=
  match goal with
  | x : Word.Interface.word.rep _ |- _ => clear x
  | x : Semantics.word |- _ => clear x
  | x : Init.Byte.byte |- _ => clear x
  | x : Semantics.locals |- _ => clear x
  | x : Semantics.trace |- _ => clear x
  | x : Syntax.cmd |- _ => clear x
  | x : Syntax.expr |- _ => clear x
  | x : coqutil.Map.Interface.map.rep |- _ => clear x
  | x : BinNums.Z |- _ => clear x
  | x : unit |- _ => clear x
  | x : bool |- _ => clear x
  | x : list _ |- _ => clear x
  | x : nat |- _ => clear x
  | x := _ : Word.Interface.word.rep _ |- _ => clear x
  | x := _ : Semantics.word |- _ => clear x
  | x := _ : Init.Byte.byte |- _ => clear x
  | x := _ : Semantics.locals |- _ => clear x
  | x := _ : Semantics.trace |- _ => clear x
  | x := _ : Syntax.cmd |- _ => clear x
  | x := _ : Syntax.expr |- _ => clear x
  | x := _ : coqutil.Map.Interface.map.rep |- _ => clear x
  | x := _ : BinNums.Z |- _ => clear x
  | x := _ : unit |- _ => clear x
  | x := _ : bool |- _ => clear x
  | x := _ : list _ |- _ => clear x
  | x := _ : nat |- _ => clear x
  | |- forall _, _ => intros
  | |- let _ := _ in _ => intros
  | |- dlet.dlet ?v (fun x => ?P) => change (let x := v in P); intros
  | _ => progress (cbn [Semantics.interp_binop] in * )
  | H: exists x, _ |- _ => destruct H as [x H]
  | H: _ /\ _ |- _ => lazymatch type of H with
                      | _ <  _ <  _ => fail
                      | _ <  _ <= _ => fail
                      | _ <= _ <  _ => fail
                      | _ <= _ <= _ => fail
                      | _ => destruct H
                      end
  | x := ?y |- ?G => is_var y; subst x
  | H: ?x = word.of_Z ?y |- _ => match isZcst y with
                                 | true => subst x
                                 end
  | x := word.of_Z ?y |- _ => match isZcst y with
                              | true => subst x
                              end
  | H: ?x = ?y |- _ => constr_eq x y; clear H
  | |- ~ _ => intro
  | H: _ :: _ = _ :: _ |- _ => injection H as
  | H: Some _ = Some _ |- _ => injection H as
  end.

Import WeakestPrecondition.

Ltac locals_step :=
  match goal with
  | _ => cleanup_step
  | |- @list_map _ _ (@get _ _) _ _ => unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | |- @list_map _ _ _ nil _ => cbv beta match fix delta [list_map list_map_body]
  | |- @get _ _ _ _ => cbv beta delta [get]
  | |- map.get _ _ = Some ?e' =>
    let e := rdelta e' in
    is_evar e;
    let M := lazymatch goal with |- @map.get _ _ ?M _ _ = _ => M end in
    let __ := match M with @Semantics.locals _ => idtac end in
    let k := lazymatch goal with |- map.get _ ?k = _ => k end in
    once (let v := multimatch goal with x := context[@map.put _ _ M _ k ?v] |- _ => v end in
          (* cbv is slower than this, cbv with whitelist would have an enormous whitelist, cbv delta for map is slower than this, generalize unrelated then cbv is slower than this, generalize then vm_compute is slower than this, lazy is as slow as this: *)
          unify e v; exact (eq_refl (Some v)))
  | |- @coqutil.Map.Interface.map.get _ _ (@Semantics.locals _) _ _ = Some ?v =>
    let v' := rdelta v in is_evar v'; (change v with v'); exact eq_refl
  | |- ?x = ?y =>
    let y := rdelta y in is_evar y; change (x=y); exact eq_refl
  | |- ?x = ?y =>
    let x := rdelta x in is_evar x; change (x=y); exact eq_refl
  | |- ?x = ?y =>
    let x := rdelta x in let y := rdelta y in constr_eq x y; exact eq_refl
  | |- exists l', Interface.map.of_list_zip ?ks ?vs = Some l' /\ _ =>
    letexists; split; [exact eq_refl|] (* TODO: less unification here? *)
  | |- exists l', Interface.map.putmany_of_list_zip ?ks ?vs ?l = Some l' /\ _ =>
    letexists; split; [exact eq_refl|] (* TODO: less unification here? *)
  | |- exists x, ?P /\ ?Q =>
    let x := fresh x in refine (let x := _ in ex_intro (fun x => P /\ Q) x _);
                        split; [solve [repeat locals_step]|]
  end.

Ltac expr_step :=
  match goal with
  | _ => locals_step
  | |- @list_map _ _ (@expr _ _ _) _ _ => unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | |- @expr _ _ _ _ _ => unfold1_expr_goal; cbv beta match delta [expr_body]
  | |- @dexpr _ _ _ _ _ => cbv beta delta [dexpr]
  | |- @dexprs _ _ _ _ _ => cbv beta delta [dexprs]
  | |- @literal _ _ _ => cbv beta delta [literal]
  | |- @load _ _ _ _ _ => eapply load_field'';
       once (match goal with
             (* backtrack over choice of Hm in case there are several *)
             | Hm: seps ?lm ?m |- exists l, seps l ?m /\ _ =>
               exists lm; split; [exact Hm|];
               let n := eval cbv [List.length] in (List.length lm) in
                   (* backtrack over choice of i *)
                   let i := pick_nat n in
                   eexists i; split; [cbv [List.nth_error]; reflexivity|];
                   split; [ repeat (lookup_done || lookup_field_step) |]
             end)
  | |- @eq (@coqutil.Map.Interface.map.rep _ _ (@Semantics.locals _)) _ _ =>
    eapply SortedList.eq_value; exact eq_refl
  | |- True => exact I
  | |- False \/ _ => right
  | |- _ \/ False => left
  end.

Import Syntax.

Inductive snippet :=
| SSet(x: string)(e: expr)
| SIf(cond: expr)(merge: bool)
| SEnd
| SElse.

Inductive note_wrapper: string -> Type := mkNote(s: string): note_wrapper s.
Notation "s" := (note_wrapper s) (at level 200, only printing).
Ltac add_note s := let n := fresh "Note" in pose proof (mkNote s) as n; move n at top.

Ltac add_snippet s :=
  lazymatch s with
  | SSet ?y ?e => eapply assignment with (x := y) (a := e); repeat expr_step
  | SIf ?cond false => eapply if_split with (c := cond);
                       [ repeat expr_step
                       | intros
                       | intros; add_note "'else' expected" ]
  | SEnd => eapply exec.skip
  | SElse => lazymatch goal with
             | H: note_wrapper "'else' expected" |- _ => clear H
             end
  end.


Ltac ring_simplify_hyp_rec t H :=
  lazymatch t with
  | ?a = ?b => ring_simplify_hyp_rec a H || ring_simplify_hyp_rec b H
  | word.unsigned ?a => ring_simplify_hyp_rec a H
  | word.of_Z ?a => ring_simplify_hyp_rec a H
  | _ => progress ring_simplify t in H
  end.

Ltac ring_simplify_hyp H :=
  let t := type of H in ring_simplify_hyp_rec t H.

Lemma if_then_1_else_0_eq_0: forall (b: bool),
    word.unsigned (if b then word.of_Z 1 else word.of_Z 0) = 0 ->
    b = false.
Proof. intros; destruct b; [exfalso|reflexivity]. ZnWords. Qed.

Lemma if_then_1_else_0_neq_0: forall (b: bool),
    word.unsigned (if b then word.of_Z 1 else word.of_Z 0) <> 0 ->
    b = true.
Proof. intros; destruct b; [reflexivity|exfalso]. ZnWords. Qed.

Ltac simpli_getEq t :=
  match t with
  | context[@word.and ?wi ?wo (if ?b1 then _ else _) (if ?b2 then _ else _)] =>
    constr:(@word.and_bool_to_word wi wo _ b1 b2)
  | context[@word.unsigned ?wi ?wo (word.of_Z ?x)] => constr:(@word.unsigned_of_Z_nowrap wi wo _ x)
  | context[@word.of_Z ?wi ?wo (word.unsigned ?x)] => constr:(@word.of_Z_unsigned wi wo _ x)
  end.

(* random simplifications that make the goal easier to prove *)
Ltac simpli_step :=
  match goal with
  | |- _ => cleanup_step
  | |- _ => progress (rewr simpli_getEq in * by ZnWords)
  | H: word.unsigned (if ?b then _ else _) = 0 |- _ => apply if_then_1_else_0_eq_0 in H
  | H: word.unsigned (if ?b then _ else _) <> 0 |- _ => apply if_then_1_else_0_neq_0 in H
  | H: word.eqb ?x ?y = true  |- _ => apply (word.eqb_true  x y) in H
  | H: word.eqb ?x ?y = false |- _ => apply (word.eqb_false x y) in H
  | H: andb ?b1 ?b2 = true |- _ => apply (Bool.andb_true_iff b1 b2) in H
  | H: andb ?b1 ?b2 = false |- _ => apply (Bool.andb_false_iff b1 b2) in H
  | H: orb ?b1 ?b2 = true |- _ => apply (Bool.orb_true_iff b1 b2) in H
  | H: orb ?b1 ?b2 = false |- _ => apply (Bool.orb_false_iff b1 b2) in H
  | H: word.of_Z ?x = word.of_Z ?y |- _ =>
    assert (x = y) by (apply (word.of_Z_inj_small H); ZnWords); clear H
  | |- _ => progress simpl (bytes_per _) in *
  end.

(* random simplifications that make the goal more readable and might be expensive *)
Ltac pretty_step :=
  match goal with
  | H: _ |- _ => ring_simplify_hyp H
  | H: ?T |- _ => clear H; assert_succeeds (assert T by ZnWords)
  end ||
  simpl_Z_nat.

Hint Unfold validPacket needsARPReply : prover_unfold_hints.

(* partially proves postconditions, trying to keep the goal readable *)
Ltac prover_step :=
  match goal with
  | |- _ => progress locals_step
  | |- _ => progress simpli_step
  | |- ?P /\ ?Q => assert_fails (is_lia_prop P; is_lia_prop Q); split
  | |- _ => ZnWords
  | |- ?P \/ ?Q =>
    let t := (repeat prover_step; ZnWords) in
    tryif (assert_succeeds (assert (P -> False) by t)) then
      tryif (assert_succeeds (assert (Q -> False) by t)) then
        fail 1 "you are trying to prove False"
      else
        right
    else
      tryif (assert_succeeds (assert (Q -> False) by t)) then
        left
      else
        fail "not sure whether to try left or right side of \/"
  | |- _ => solve [auto]
  | |- _ => progress autounfold with prover_unfold_hints in *
  end.

Ltac after_snippet := repeat simpli_step; repeat simpli_step.
(* For debugging, this can be useful:
Ltac after_snippet ::= idtac.
*)

  Hint Resolve EthernetPacket_spec: TypeSpec_instances.
  Hint Resolve ARPPacket_spec: TypeSpec_instances.

  Goal TypeSpec (EthernetPacket ARPPacket). eauto 2 with TypeSpec_instances. all: fail. Abort.

  Ltac index_of_getter getter fields :=
    lazymatch fields with
    | FField getter _ _ :: _ => constr:(O)
    | FField _ _ _ :: ?tail => let r := index_of_getter getter tail in constr:(S r)
    end.

  Ltac offset_of_getter getter :=
    lazymatch type of getter with
    | ?R -> ?F =>
      let sp := constr:(ltac:(eauto 2 with TypeSpec_instances) : TypeSpec R) in
      lazymatch eval hnf in sp with
      | TStruct ?fields =>
        let i := index_of_getter getter fields in
        lazymatch eval cbn in (fun r: R => offset r fields i) with
        (* value-dependent offsets are not supported here *)
        | fun _ => ?x => x
        end
      end
    end.

  Goal False.
    let ofs := offset_of_getter (@dstMAC ARPPacket) in idtac ofs.
    let ofs := offset_of_getter (@srcMAC ARPPacket) in idtac ofs.
    let ofs := offset_of_getter (@etherType ARPPacket) in idtac ofs.
    let ofs := offset_of_getter (@payload ARPPacket) in idtac ofs.
    let ofs := offset_of_getter plen in idtac ofs.
    let ofs := offset_of_getter spa in idtac ofs.
  Abort.

Tactic Notation "$" constr(s) "$" := add_snippet s; after_snippet.

Notation "/*number*/ e" := e (in custom bedrock_expr at level 0, e constr at level 0).

Notation "base @ getter" :=
  (expr.op bopname.add base (expr.literal ltac:(let ofs := offset_of_getter getter in exact ofs)))
  (in custom bedrock_expr at level 6, left associativity, only parsing,
   base custom bedrock_expr, getter constr).

Declare Custom Entry snippet.

Notation "*/ s /*" := s (s custom snippet at level 100).
Notation "x = e ;" := (SSet x e) (in custom snippet at level 0, x ident, e custom bedrock_expr).
Notation "'if' ( e ) '/*merge*/' {" := (SIf e true) (in custom snippet at level 0, e custom bedrock_expr).
Notation "'if' ( e ) '/*split*/' {" := (SIf e false) (in custom snippet at level 0, e custom bedrock_expr).
Notation "}" := SEnd (in custom snippet at level 0).
Notation "'else' {" := SElse (in custom snippet at level 0).

Set Default Goal Selector "1".

  Definition memcpy: (string * {f: list string * list string * cmd &
    forall e t m dstA srcA L srcData oldDstData R,
    seps [array ptsto /[1] srcA srcData; array ptsto /[1] dstA oldDstData; R] m ->
    \[L] = len srcData ->
    \[L] = len oldDstData ->
    vc_func e f t m [dstA; srcA; L] (fun t' m' retvs =>
      retvs = [] /\
      seps [array ptsto /[1] srcA srcData; array ptsto /[1] dstA srcData; R] m')}).
  Admitted.

  Definition arp: (string * {f: list string * list string * cmd &
    forall e t m ethbufAddr ethBufData L R,
      seps [array ptsto /[1] ethbufAddr ethBufData; R] m ->
      \[L] = len ethBufData ->
      vc_func e f t m [ethbufAddr; L] (fun t' m' retvs =>
        t' = t /\ (
        (* Success: *)
        (retvs = [/[1]] /\ exists request,
            validPacket request /\
            needsARPReply request /\
            seps [dataAt (EthernetPacket_spec ARPPacket_spec) ethbufAddr request; R] m /\
            seps [dataAt (EthernetPacket_spec ARPPacket_spec) ethbufAddr (ARPReply request); R] m') \/
        (* Failure: *)
        (retvs = [/[0]] /\ (~ exists request,
            validPacket request /\
            needsARPReply request /\
            seps [dataAt (EthernetPacket_spec ARPPacket_spec) ethbufAddr request; R] m) /\
            seps [array ptsto /[1] ethbufAddr ethBufData; R] m')
      ))}).
    pose "ethbuf" as ethbuf. pose "ln" as ln. pose "doReply" as doReply. pose "tmp" as tmp.
    refine ("arp", existT _ ([ethbuf; ln], [doReply], _) _).
    intros. cbv [vc_func]. letexists. split. 1: subst l; reflexivity. intros.

    $*/
    doReply = /*number*/0; /*$. $*/
    if (ln == /*number*/64) /*split*/ {
      /*$. edestruct (bytesToEthernetARPPacket ethbufAddr _ H0) as (pk & A). seprewrite_in A H.
           change (seps [dataAt (EthernetPacket_spec ARPPacket_spec) ethbufAddr pk; R] m) in H. $*/
      if ((load2(ethbuf @ (@etherType ARPPacket)) == ETHERTYPE_ARP_LE) &
          (load2(ethbuf @ (@payload ARPPacket) @ htype) == HTYPE_LE) &
          (load2(ethbuf @ (@payload ARPPacket) @ ptype) == PTYPE_LE) &
          (load1(ethbuf @ (@payload ARPPacket) @ hlen) == HLEN) &
          (load1(ethbuf @ (@payload ARPPacket) @ plen) == PLEN) &
          (load2(ethbuf @ (@payload ARPPacket) @ oper) == coq:(LittleEndian.combine 2 OPER_REQUEST)) &
          (load4(ethbuf @ (@payload ARPPacket) @ tpa) == coq:(LittleEndian.combine 4 cfg.(myIPv4))))
      /*split*/ { /*$.

        (* TODO check if tpa equals our IP *)

        (* copy sha and spa from the request into tha and tpa for the reply (same buffer), 6+4 bytes *)
        (* memcpy(ethbuf @ (@payload ARPPacket) @ tha, ethbuf @ (@payload ARPPacket) @ sha, /*number*/10); *)

        $*/
        doReply = /*number*/1; /*$.
        (* TODO *) $*/
      } /*$ .

{

repeat prover_step.

exists pk.

repeat prover_step.

all: exact TODO.
}
$*/
    else { /*$. (* nothing to do *) $*/
    } /*$.
      eexists.
      split. 1: reflexivity.
      split. 1: reflexivity.
      right.
      split. 1: reflexivity.
      exact TODO.
    Unshelve.
    all: try exact (word.of_Z 0).
    all: try exact nil.
    all: try (exact (fun _ => False)).
    all: try exact TODO.
  Defined. (* takes ca 50s *)

  Goal False.
    let r := eval unfold arp in match arp with
                                | (fname, existT _ (argnames, retnames, body) _) => body
                                end
      in pose r.
  Abort.

End WithParameters.
