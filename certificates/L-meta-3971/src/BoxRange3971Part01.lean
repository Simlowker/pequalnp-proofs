import Boxes3971Part01
import Catalog3971
namespace PetersenNegated3971
theorem boxRange1 (r : Fin 32) : let idx := 32+r.val
  checkBox (bk idx,bm idx,br idx)=true := by
  fin_cases r
  · exact box_ok32
  · exact box_ok33
  · exact box_ok34
  · exact box_ok35
  · exact box_ok36
  · exact box_ok37
  · exact box_ok38
  · exact box_ok39
  · exact box_ok40
  · exact box_ok41
  · exact box_ok42
  · exact box_ok43
  · exact box_ok44
  · exact box_ok45
  · exact box_ok46
  · exact box_ok47
  · exact box_ok48
  · exact box_ok49
  · exact box_ok50
  · exact box_ok51
  · exact box_ok52
  · exact box_ok53
  · exact box_ok54
  · exact box_ok55
  · exact box_ok56
  · exact box_ok57
  · exact box_ok58
  · exact box_ok59
  · exact box_ok60
  · exact box_ok61
  · exact box_ok62
  · exact box_ok63
end PetersenNegated3971
