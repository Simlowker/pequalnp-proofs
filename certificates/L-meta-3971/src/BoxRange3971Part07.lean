import Boxes3971Part07
import Catalog3971
namespace PetersenNegated3971
theorem boxRange7 (r : Fin 32) : let idx := 224+r.val
  checkBox (bk idx,bm idx,br idx)=true := by
  fin_cases r
  · exact box_ok224
  · exact box_ok225
  · exact box_ok226
  · exact box_ok227
  · exact box_ok228
  · exact box_ok229
  · exact box_ok230
  · exact box_ok231
  · exact box_ok232
  · exact box_ok233
  · exact box_ok234
  · exact box_ok235
  · exact box_ok236
  · exact box_ok237
  · exact box_ok238
  · exact box_ok239
  · exact box_ok240
  · exact box_ok241
  · exact box_ok242
  · exact box_ok243
  · exact box_ok244
  · exact box_ok245
  · exact box_ok246
  · exact box_ok247
  · exact box_ok248
  · exact box_ok249
  · exact box_ok250
  · exact box_ok251
  · exact box_ok252
  · exact box_ok253
  · exact box_ok254
  · exact box_ok255
end PetersenNegated3971
