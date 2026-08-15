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

/-! ## Direct callees of the exported text driver

These names turn the otherwise opaque generated numbers into stable proof
boundaries.  Indices here are local-module indices; the corresponding Wasm
call immediate is two larger because the module has two StdIO imports. -/

theorem intoIterNext_index : «module».funcs[5]? = some func5Def := by rfl
theorem mapNext_index : «module».funcs[0]? = some func0Def := by rfl
theorem splitNext_index : «module».funcs[1]? = some func1Def := by rfl
theorem parseClosure_index : «module».funcs[2]? = some func2Def := by rfl
theorem writeFmt_index : «module».funcs[33]? = some func33Def := by rfl
theorem readLine_index : «module».funcs[37]? = some func37Def := by rfl
theorem displayArgument_index : «module».funcs[43]? = some func43Def := by rfl
theorem argumentsNew_index : «module».funcs[49]? = some func49Def := by rfl
theorem argumentsFromStr_index : «module».funcs[50]? = some func50Def := by rfl
theorem dropString_index : «module».funcs[62]? = some func62Def := by rfl
theorem dropVecU64_index : «module».funcs[68]? = some func68Def := by rfl
theorem dropIntoIterU64_index : «module».funcs[74]? = some func74Def := by rfl
theorem dropBufReader_index : «module».funcs[78]? = some func78Def := by rfl
theorem dropBufWriter_index : «module».funcs[79]? = some func79Def := by rfl
theorem stringSplit_index : «module».funcs[82]? = some func82Def := by rfl
theorem stringParse_index : «module».funcs[81]? = some func81Def := by rfl
theorem u64FromAsciiRadix_index : «module».funcs[51]? = some func51Def := by rfl
theorem u64FromStr_index : «module».funcs[53]? = some func53Def := by rfl
theorem splitInternalNext_index : «module».funcs[84]? = some func84Def := by rfl
theorem charSearcherNextMatch_index : «module».funcs[86]? = some func86Def := by rfl
theorem iteratorMap_index : «module».funcs[90]? = some func90Def := by rfl
theorem iteratorCollect_index : «module».funcs[91]? = some func91Def := by rfl
theorem vecLen_index : «module».funcs[103]? = some func103Def := by rfl
theorem vecFromElem_index : «module».funcs[105]? = some func105Def := by rfl
theorem stringNew_index : «module».funcs[110]? = some func110Def := by rfl
theorem stringDeref_index : «module».funcs[119]? = some func119Def := by rfl
theorem vecDerefMut_index : «module».funcs[122]? = some func122Def := by rfl
theorem vecIntoIter_index : «module».funcs[123]? = some func123Def := by rfl
theorem buffered_index : «module».funcs[135]? = some func135Def := by rfl
theorem allocator_index : «module».funcs[160]? = some func160Def := by rfl

theorem export_index : «module».exports =
    [{ name := "mergesort", funcIdx := 129 }] := rfl

end Project.Mergesort.FunctionSpecs
