package breu;

import org.scalatest.FunSuite
import org.scalatest._
import java.io.File
import scala.io.Source

class Regression extends FunSpec {

  val TIMEOUT = 5000

  def getListOfFiles(dir: File, extensions: List[String]): List[File] = {
    dir.listFiles.filter(_.isFile).toList.filter { file =>
      extensions.exists(file.getName.endsWith(_))
    }
  }
  
  val satSources = new File(getClass.getResource("/sat/").toURI())
  val satFiles = getListOfFiles(satSources, List(".breu"))

  // assert(Tester.testIncremental("/home/ptr/Projects/breu/target/scala-2.12/test-classes/sat/cade.breu", TIMEOUT) == breu.Result.SAT)

  describe("SAT") {
    for (f <- satFiles) {
      it(f.getName()) {
        val ret = Tester.test(f.toString, TIMEOUT)
        assert(ret == breu.Result.SAT)
      }
    }
  }

  val unsatSources = new File(getClass.getResource("/unsat/").toURI())
  val unsatFiles = getListOfFiles(unsatSources, List(".breu"))

  describe("UNSAT") {
    for (f <- unsatFiles) {
      it(f.getName()) {
        val ret = Tester.test(f.toString, TIMEOUT)
        assert(ret == breu.Result.UNSAT)
      }
    }
  }
}
