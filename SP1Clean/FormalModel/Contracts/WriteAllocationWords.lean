import SP1Clean.FormalModel.Contracts.WriteAllocation
import SP1Clean.FormalModel.Contracts.HintWords
import SP1Clean.Semantics.Host.WriteStreamBlocks

/-! # Each padded word of one authorized hint allocation

A mandatory cursor starts at word zero for every fresh node, including an empty node.
It carries the same allocation identity until the last, possibly fully padded, word.
The block and persistent queue word share their eight actual byte columns.
-/

namespace SP1Clean.WriteAllocation.Words
open Semantics.HintQueue WriteEffects

/-- Current location in a single new node's contiguous padded word inventory. -/
structure Cursor (F : Type) where
  /-- Original authorization from the fresh node allocation. -/
  contents : Contents F
  /-- Zero-based word index in that node. -/
  index : fields 3 F
  /-- Number of unpadded bytes still to place, including the current word. -/
  remaining : fields 3 F
deriving ProvableStruct
provable_struct_eval_lemmas Cursor

/-- The mandatory first word starts at zero and must consume the entire byte count. -/
def start {F : Type} [Zero F] (c : Contents F) : Cursor F := ⟨c,0,c.length⟩

/-- A private unit-demand walk local to one newly allocated pointer. -/
def cursorChannel {p : Nat} : Channel (ZMod p) Cursor where
  name := "sp1.native.write_allocation_word_cursor"
  Guarantees _ _ := True

/-- Packed bytes and their contiguous occupancy mask. -/
structure Payload (F : Type) where
  /-- All eight byte lanes, with zeroes in unused positions. -/
  bytes : fields 8 F
  /-- One for each occupied lane from the beginning of the word. -/
  mask : fields 8 F
deriving ProvableStruct
provable_struct_eval_lemmas Payload

/-- The preceding lane's occupancy; the virtual lane before zero is occupied. -/
def Payload.previous {F : Type} [One F] (r : Payload F) (i : Fin 8) : F :=
  if i.val = 0 then 1 else r.mask[i.val-1]'(by have := i.isLt; omega)

/-- Number of occupied lanes represented by one linear expression. -/
def Payload.used {F : Type} [Add F] (r : Payload F) : F :=
  r.mask[0]+r.mask[1]+r.mask[2]+r.mask[3]+r.mask[4]+r.mask[5]+r.mask[6]+r.mask[7]

/-- A full word continues, including when a separately allocated empty padding word follows. -/
def Payload.more {F : Type} (r : Payload F) : F := r.mask[7]

/-- The last padded word contains zero through seven occupied bytes. -/
def Payload.last {F : Type} [One F] [Sub F] (r : Payload F) : F := 1-r.more

/-- One data row for every word of a newly authorized node. -/
structure Row (F : Type) where
  /-- Name, current index, and unprocessed length of the genuine allocation. -/
  prior : Cursor F
  /-- Predecessor of the positive immutable pointer. -/
  predecessor : fields 3 F
  /-- Current word index plus one. -/
  nextIndex : fields 3 F
  /-- Remaining bytes after the occupied prefix. -/
  left : fields 3 F
  /-- Eight shared output lanes and their exact final extent. -/
  payload : Payload F
  /-- Number of grouped placements using this direct hint block. -/
  blockReads : F
  /-- Number of consumers of this persistent word, including later pops or endpoint reads. -/
  wordReads : F
deriving ProvableStruct
provable_struct_eval_lemmas Row

/-- Cursor after a full word; partial words end the walk. -/
def Row.next {F : Type} (r : Row F) : Cursor F := ⟨r.prior.contents,r.nextIndex,r.left⟩

/-- Word seen by persistent queue readers at their own independent multiplicity. -/
def Row.word {F : Type} [One F] [Sub F] [Add F] [Mul F] [OfNat F 256] (r : Row F) : WordRecord F :=
  ⟨r.prior.contents.pointer,r.prior.index,Word.ofBytes r.payload.bytes,r.payload.last⟩

/-- Existing public tag-4 block for a supplied hook reply. -/
def Row.returned {F : Type} [Add F] [OfNat F 4] (r : Row F) : StreamBlock F :=
  ⟨4,r.prior.contents.reply,r.prior.contents.index,r.prior.index,r.payload.used,r.payload.bytes⟩

/-- Private tag-14 block consumed by guest placement, keyed by the same fresh immutable pointer. -/
def Row.direct {F : Type} [Add F] [Zero F] [OfNat F 14] (r : Row F) : StreamBlock F :=
  ⟨14,r.prior.contents.pointer,0,r.prior.index,r.payload.used,r.payload.bytes⟩

end SP1Clean.WriteAllocation.Words
