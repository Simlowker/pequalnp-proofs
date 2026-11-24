import Boxes3971Part06
import Catalog3971
namespace PetersenNegated3971
theorem boxRange6 (r : Fin 32) : let idx := 192+r.val
  checkBox (bk idx,bm idx,br idx)=true := by
  fin_cases r
  · exact box_ok192
  · exact box_ok193
  · exact box_ok194
  · exact box_ok195
  · exact box_ok196
  · exact box_ok197
  · exact box_ok198
  · exact box_ok199
  · exact box_ok200
  · exact box_ok201
  · exact box_ok202
  · exact box_ok203
  · exact box_ok204
  · exact box_ok205
  · exact box_ok206
  · exact box_ok207
  · exact box_ok208
  · exact box_ok209
  · exact box_ok210
  · exact box_ok211
  · exact box_ok212
  · exact box_ok213
  · exact box_ok214
  · exact box_ok215
  · exact box_ok216
  · exact box_ok217
  · exact box_ok218
  · exact box_ok219
  · exact box_ok220
  · exact box_ok221
  · exact box_ok222
  · exact box_ok223
end PetersenNegated3971
