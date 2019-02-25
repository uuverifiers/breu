object BREUtest {

  def checkTO() = {
  }

  def main(args : Array[String]) : Unit = {
    if (args.length < 1)
      return println("Usage: BREUtest input.breu [timeout]")
    val timeout : Long =
      if (args.length < 2)
        5000
      else
        args(1).toLong

    val t0 = System.nanoTime()
    val res = breu.Tester.test(args(0), timeout)
    val t1 = System.nanoTime()
    val runTime = t1 - t0
    println(res)
    println("Time: " + runTime/1000000 + " ms")    
  }
}
