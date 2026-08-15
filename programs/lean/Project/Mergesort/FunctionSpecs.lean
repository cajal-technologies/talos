import Project.Mergesort.Program
import Project.Mergesort.Pure

/-!
# Function map and contracts for the original generated merge-sort module

The unchanged Rust program compiles to 255 local functions. The proof is
layered around the small subset that lies on the successful exported path:

* `func125` is the monomorphised `merge::<u64>` body;
* `func126` is the monomorphised recursive `mergesort::<u64>` body;
* `func127` is the exported text-IO driver;
* `func7`--`func9`, `func93`--`func97` are slice splitting and copying;
* the remaining driver callees implement buffered IO, decimal parsing,
  allocation, iteration, decimal formatting, and destruction.

Call immediates use the Wasm function index space, which starts with the two
StdIO imports. Thus local `func125` is called with index `127`, local
`func126` with index `128`, and local `func127` is exported at index `129`.
-/

namespace Project.Mergesort.FunctionSpecs

open Wasm

def mergeFunction : Wasm.Function := func125Def
def sortFunction : Wasm.Function := func126Def
def exportFunction : Wasm.Function := func127Def

def rangeFunction : Wasm.Function := func7Def
def rangeToFunction : Wasm.Function := func8Def
def rangeFromFunction : Wasm.Function := func9Def
def copySliceImplFunction : Wasm.Function := func93Def
def cloneFromSliceFunction : Wasm.Function := func94Def
def specCloneFromFunction : Wasm.Function := func95Def
def splitAtUncheckedFunction : Wasm.Function := func96Def
def splitAtFunction : Wasm.Function := func97Def

theorem merge_body : mergeFunction.body = func125 := rfl
theorem sort_body : sortFunction.body = func126 := rfl
theorem export_body : exportFunction.body = func127 := rfl

theorem range_body : rangeFunction.body = func7 := rfl
theorem rangeTo_body : rangeToFunction.body = func8 := rfl
theorem rangeFrom_body : rangeFromFunction.body = func9 := rfl
theorem copySliceImpl_body : copySliceImplFunction.body = func93 := rfl
theorem cloneFromSlice_body : cloneFromSliceFunction.body = func94 := rfl
theorem specCloneFrom_body : specCloneFromFunction.body = func95 := rfl
theorem splitAtUnchecked_body : splitAtUncheckedFunction.body = func96 := rfl
theorem splitAt_body : splitAtFunction.body = func97 := rfl

theorem merge_index : «module».funcs[125]? = some mergeFunction := by
  rfl

theorem sort_index : «module».funcs[126]? = some sortFunction := by
  rfl

theorem range_index : «module».funcs[7]? = some rangeFunction := by rfl
theorem rangeTo_index : «module».funcs[8]? = some rangeToFunction := by rfl
theorem rangeFrom_index : «module».funcs[9]? = some rangeFromFunction := by rfl
theorem copySliceImpl_index :
    «module».funcs[93]? = some copySliceImplFunction := by rfl
theorem cloneFromSlice_index :
    «module».funcs[94]? = some cloneFromSliceFunction := by rfl
theorem specCloneFrom_index :
    «module».funcs[95]? = some specCloneFromFunction := by rfl
theorem splitAtUnchecked_index :
    «module».funcs[96]? = some splitAtUncheckedFunction := by rfl
theorem splitAt_index :
    «module».funcs[97]? = some splitAtFunction := by rfl

theorem export_index : «module».exports =
    [{ name := "mergesort", funcIdx := 129 }] := rfl

end Project.Mergesort.FunctionSpecs
