import Lake
open Lake DSL System

-- TODO: switch to these once the releases adopt the expected format
-- def tag : String := "nightly-2021-11-11"
-- def releaseRepo : String := "leanprover-community/mathport"
-- def tarName : String := "lean3-binport.tar.gz"

def tag : String := "test"
def releaseRepo : String := "dselsam/mathport"
def tarName : String := "leanbin-oleans.tar.gz"

def fetchOleans (dir : FilePath) : OpaqueTarget := { info := (), task := fetch } where
  fetch := async do
    IO.FS.createDirAll libDir
    let oldTrace := Hash.ofString (← Git.headRevision dir)
    buildFileUnlessUpToDate (libDir / tarName) oldTrace do
      downloadOleans
      untarOleans

  downloadOleans : BuildM PUnit := Lake.proc {
      cmd := "wget",
      args := #[s!"https://github.com/{releaseRepo}/releases/download/{tag}/{tarName}"]
      cwd := libDir.toString
    }

  untarOleans : BuildM PUnit := Lake.proc {
      cmd := "tar",
      args := #["-xzvf", tarName]
      cwd := libDir.toString
    }

  libDir : FilePath := dir / "build" / "lib"

package leanbin (dir) {
  libRoots := #[]
  libGlobs := #[`Leanbin]
  extraDepTarget := fetchOleans dir
  defaultFacet := PackageFacet.oleans
  dependencies := #[{
    name := "mathlib",
    src := Source.git "https://github.com/dselsam/mathlib4.git" "5366ff9252f9001fc10e610795efd259fd4b8dc6"
  }]
}
