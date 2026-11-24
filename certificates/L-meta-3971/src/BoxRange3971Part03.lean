import Boxes3971Part03
import Catalog3971
namespace PetersenNegated3971
theorem boxRange3 (r : Fin 32) : let idx := 96+r.val
  checkBox (bk idx,bm idx,br idx)=true := by
  fin_cases r
  · exact box_ok96
  · exact box_ok97
  · exact box_ok98
  · exact box_ok99
  · exact box_ok100
  · exact box_ok101
  · exact box_ok102
  · exact box_ok103
  · exact box_ok104
  · exact box_ok105
  · exact box_ok106
  · exact box_ok107
  · exact box_ok108
  · exact box_ok109
  · exact box_ok110
  · exact box_ok111
  · exact box_ok112
  · exact box_ok113
  · exact box_ok114
  · exact box_ok115
  · exact box_ok116
  · exact box_ok117
  · exact box_ok118
  · exact box_ok119
  · exact box_ok120
  · exact box_ok121
  · exact box_ok122
  · exact box_ok123
  · exact box_ok124
  · exact box_ok125
  · exact box_ok126
  · exact box_ok127
end PetersenNegated3971
