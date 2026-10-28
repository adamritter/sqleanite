import SQLeanite.CoreFileAdapter.Paths
import SQLeanite.PhysicalWALRecovery

/-!
# Write-ahead log for arbitrary Core schemas

`PhysicalWALRecovery` is already schema-agnostic: it works over
`GrowableStorage.Image`, a page-level picture of the file, and its recovery
theorems never mention a row type. Only the final `forTree` specialization was
tied to the fixed three-column table.

This module supplies the matching specialization for the arbitrary-schema core,
using `CoreFileAdapter.storageImage` as the bridge from a `CoreFile.Image` to
the page-level image the WAL protocol consumes. With it, the WAL path no longer
depends on the fixed-schema engine.
-/

namespace SQLeanite.CoreWAL

open PhysicalWALRecovery

/-- Page count of an encoded Core image, as the WAL header records it. -/
def imagePageCount (image : CoreFile.Image) : Nat :=
  (CoreFileAdapter.storageImage image).pageCount

/-- The WAL frames that publish a whole Core image. -/
def forCoreImage (header : PhysicalWAL.Header) (image : CoreFile.Image)
    (fits : imagePageCount image < 2 ^ 32) : PhysicalWAL.WAL :=
  { header
    frames := frames (CoreFileAdapter.storageImage image) fits }

theorem decode_encode_forCoreImage (header : PhysicalWAL.Header)
    (image : CoreFile.Image) (fits : imagePageCount image < 2 ^ 32) :
    PhysicalWAL.decode (forCoreImage header image fits).encode =
      some (forCoreImage header image fits) :=
  PhysicalWAL.decode_encode _

/-- **WAL recovery for arbitrary schemas.** Replaying the frames of a committed
Core image over any main file yields a page image equivalent to that Core image,
so a reader that recovers through the WAL observes exactly the committed
database and never a partial one. -/
theorem recover_forCoreImage (main : Image) (header : PhysicalWAL.Header)
    (image : CoreFile.Image) (fits : imagePageCount image < 2 ^ 32)
    (positive : 0 < imagePageCount image) :
    ∃ recovered,
      recover main (forCoreImage header image fits) = some recovered ∧
        GrowableStorage.Image.Equiv recovered
          (CoreFileAdapter.storageImage image) := by
  rcases recover_frames_equiv main (CoreFileAdapter.storageImage image)
    fits positive header with ⟨recovered, recoveredEq, equivalent⟩
  exact ⟨recovered, recoveredEq, equivalent⟩

end SQLeanite.CoreWAL
