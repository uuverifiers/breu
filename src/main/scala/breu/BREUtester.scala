package breu;

object BREUtester {

  def checkTO() = {
  }

  def test(file : String) : breu.Result.Value = {
    val cons = new breu.BREUConstructor[String,String]()

    val input = io.Source.fromFile(file).getLines.toList

    var section = ""

    val dPattern = "(.*)=(.*)".r
    val fPattern = "(.*)\\((.*)\\)=(.*)".r
    val gPattern = "(.*=\\?.*\\|?)+".r    

    for (l <- input) {
      l.trim() match {
        case dPattern(t,d) if section == "domains" => cons.addDomain(t, d.split(",").toSet)
        case fPattern(f,ts,t) if section == "globals" => cons.addGlobalFunction(f, ts.split(","), t)
        case fPattern(f,ts,t) if section == "problem" => cons.addFunction(f, ts.split(","), t)
        case gPattern(sgoals) => {
          val sgPattern = "(.*)=\\?(.*)".r
          val sgs = 
            for (sg <- sgoals.split("\\|")) yield {
              sg match {
                case sgPattern(lhs, rhs) => (lhs.toString, rhs.toString)
              }
            }
          cons.addGoal(sgs.toList)
        }
        case "DOMAINS" => section = "domains"
        case "GLOBALS" => section = "globals"
        case "PROBLEM" => {
          section = "problem"
          cons.newSubproblem()
        }
      }
    }

    cons.solveLazy()
  }
}
