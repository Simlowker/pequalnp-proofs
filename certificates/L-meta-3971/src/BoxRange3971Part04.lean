import Boxes3971Part04
import Catalog3971
namespace PetersenNegated3971
theorem boxRange4 (r : Fin 32) : let idx := 128+r.val
  checkBox (bk idx,bm idx,br idx)=true := by
  fin_cases r
  · exact box_ok128
  · exact box_ok129
  · exact box_ok130
  · exact box_ok131
  · exact box_ok132
  · exact box_ok133
  · exact box_ok134
  · exact box_ok135
  · exact box_ok136
  · exact box_ok137
  · exact box_ok138
  · exact box_ok139
  · exact box_ok140
  · exact box_ok141
  · exact box_ok142
  · exact box_ok143
  · exact box_ok144
  · exact box_ok145
  · exact box_ok146
  · exact box_ok147
  · exact box_ok148
  · exact box_ok149
  · exact box_ok150
  · exact box_ok151
  · exact box_ok152
  · exact box_ok153
  · exact box_ok154
  · exact box_ok155
  · exact box_ok156
  · exact box_ok157
  · exact box_ok158
  · exact box_ok159
end PetersenNegated3971
