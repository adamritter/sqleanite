import SQLeanite.CoreLazyFileEngine
import SQLeanite.CoreWALFileEngine
import SQLeanite.ProcessLock

/-!
# Production Core runtime import surface

`Main.lean` deliberately imports this narrow module instead of the library
umbrella. The umbrella also exposes the legacy in-memory SQL interpreter as a
test/conformance fixture; keeping that fixture out of the executable import
cone makes the claim that every shipped command uses `Core` mechanically true.
-/
