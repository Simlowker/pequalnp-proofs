import Boxes3971Part05
import Catalog3971
namespace PetersenNegated3971
theorem boxRange5 (r : Fin 32) : let idx := 160+r.val
  checkBox (bk idx,bm idx,br idx)=true := by
  fin_cases r
  · exact box_ok160
  · exact box_ok161
  · exact box_ok162
  · exact box_ok163
  · exact box_ok164
  · exact box_ok165
  · exact box_ok166
  · exact box_ok167
  · exact box_ok168
  · exact box_ok169
  · exact box_ok170
  · exact box_ok171
  · exact box_ok172
  · exact box_ok173
  · exact box_ok174
  · exact box_ok175
  · exact box_ok176
  · exact box_ok177
  · exact box_ok178
  · exact box_ok179
  · exact box_ok180
  · exact box_ok181
  · exact box_ok182
  · exact box_ok183
  · exact box_ok184
  · exact box_ok185
  · exact box_ok186
  · exact box_ok187
  · exact box_ok188
  · exact box_ok189
  · exact box_ok190
  · exact box_ok191
end PetersenNegated3971
