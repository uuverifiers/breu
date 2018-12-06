package breu;

import org.scalatest.FunSuite
import org.scalatest._
import java.io.File
import scala.io.Source

class Incremental extends FunSpec {

  val X = "X"
  val Y = "Y"
  val a = "a"
  val b = "b"
  val c = "c"

  def baseConstructor() = {
    val con = new Constructor[String, String](true)
    con.addDomain(a, Set(a))
    con.addDomain(b, Set(b))
    con.addDomain(c, Set(c))        
    con.addDomain(X, Set(X, c, b, a))
    con.addDomain(Y, Set(Y, X, c, b, a))
    con
  }

  describe("Inc. 1") {


    it("No blocking clauses") {

      val con = baseConstructor()
      println("No blocking clauses")
      val sp1 = con.newSubproblem()
      con.addGoal(List((X, a)))
      con.addGoal(List((X, b)))
      con.addGoal(List((X, c)))

      var res = con.solveLazy()
      assert(res == Result.SAT)

      val sp2 = con.newSubproblem()
      con.addGoal(List((Y, b)))
      

      res = con.solveLazy()
      assert(res == Result.SAT)

      val sp3 = con.newSubproblem()
      con.addGoal(List((X, b)))
      res = con.solveLazy()
      assert(res == Result.SAT)
    }

    it("With blocking clauses") {
      println("With blocking clauses")
      val con = baseConstructor()      
      val sp1 = con.newSubproblem()
      con.addGoal(List((X, a)))
      con.addGoal(List((X, b)))
      con.addGoal(List((X, c)))

      var res = con.solveLazy()
      assert(res == Result.SAT)

      val sp2 = con.newSubproblem()
      con.addGoal(List((Y, b)))
      

      res = con.solveLazy(con.blockingClauses)
      assert(res == Result.SAT)

      val sp3 = con.newSubproblem()
      con.addGoal(List((X, b)))
      res = con.solveLazy(con.blockingClauses)
      assert(res == Result.SAT) 
    }    
  }
}
