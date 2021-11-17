import Lake
open Lake DSL System

def tag : String := "nightly-2021-11-17"
def releaseRepo : String := "leanprover-community/mathport"
def tarName : String := "mathlib3-binport.tar.gz"

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

package mathbin (dir) {
  libRoots := #[]
  libGlobs := #[`Mathbin]
  extraDepTarget := fetchOleans dir
  defaultFacet := PackageFacet.oleans
  dependencies := #[{
    name := "leanbin",
    src := Source.git "https://github.com/leanprover-community/mathport.git" "master",
    dir := "Lean4Packages/leanbin"
  }]
}
