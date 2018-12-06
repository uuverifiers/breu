package breu;

import org.scalatest.FunSuite
import org.scalatest._
import java.io.File
import scala.io.Source

class Incremental extends FunSpec {

  describe("Inc. 1") {
    val con = new Constructor[String, String](true)
    val X = "X"
    val Y = "Y"
    val a = "a"
    val b = "b"
    val c = "c"

    con.addDomain(a, Set(a))
    con.addDomain(b, Set(b))
    con.addDomain(c, Set(c))        
    con.addDomain(X, Set(X, c, b, a))
    con.addDomain(Y, Set(Y, X, c, b, a))    

    it("No blocking clauses") {
      // println("<< SP 1 >>")
      val sp1 = con.newSubproblem()
      con.addGoal(List((X, a)))
      con.addGoal(List((X, b)))
      con.addGoal(List((X, c)))

      var res = con.solveLazy()
      assert(res == Result.SAT)
      println("RES: " + res)
      println("BC: " + con.blockingClauses)
      println("MODEL: " + con.model)

      // println("<< SP 2 >>")      
      val sp2 = con.newSubproblem()
      con.addGoal(List((Y, b)))
      

      res = con.solveLazy()
      assert(res == Result.SAT)
      // println("RES: " + res)
      // println("BC: " + con.getBlockingClauses())
      // println("MODEL: " + con.getModel())


      // println("<< SP 3 >>")
      val sp3 = con.newSubproblem()
      con.addGoal(List((X, b)))
      // println(con)
      // res = con.solveLazy(con.getBlockingClauses())
      res = con.solveLazy()
      assert(res == Result.SAT)
      // println("RES: " + res)
      // println("BC: " + con.getBlockingClauses())
      // println("MODEL: " + con.getModel())      
    }

    // it("Step 3 - UNSAT") {
    //   sp2 = con.newSubproblem()
    //   con.addGoal(sp2, List((a, b)))
    //   val res = con.solveLazy()
    //   assert(res == Result.UNSAT)
    // }

    // it("Step 4 - UNSAT") {
    //   con.addFunction(sp2, (g, List(X), a))
    //   con.addFunction(sp2, (g, List(b), b))      
    //   val res = con.solveLazy()
    //   assert(res == Result.UNSAT)
    // }

    // it("Step 5 - SAT") {
    //   con.addFunction(sp1, (f, List(b), b))
    //   val res = con.solveLazy()
    //   assert(res == Result.SAT)
    // }                
  }
}
