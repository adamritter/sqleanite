import Lake

open System Lake DSL

package sqleanite

target vfsO pkg : FilePath := Job.async do
  let source ← inputFile (pkg.dir / "native" / "sqleanite_vfs.c") false
  let lean ← getLeanInstall
  -- Recompile the existing OS shim when the Lean runtime headers change.
  let object ← buildO (pkg.buildDir / "native" / "sqleanite_vfs.o") source
    #["-I", lean.includeDir.toString] #["-fPIC"] "cc" getLeanTrace
  object.await

@[default_target]
lean_lib SQLeanite where
  moreLinkObjs := #[vfsO]

@[default_target]
lean_exe sqleanite where
  root := `Main
  supportInterpreter := true

@[default_target]
lean_exe sqleanite_tests where
  root := `Tests

lean_exe sqleanite_legacy_server where
  root := `LegacyServerMain

-- A default target because `scripts/reproduce-all.sh` reports the localized
-- commit curve, and that step cannot run without this binary.
@[default_target]
lean_exe localized_scaling where
  root := `LocalizedScalingMain
