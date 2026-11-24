import Boxes3971Part02
import Catalog3971
namespace PetersenNegated3971
theorem boxRange2 (r : Fin 32) : let idx := 64+r.val
  checkBox (bk idx,bm idx,br idx)=true := by
  fin_cases r
  · exact box_ok64
  · exact box_ok65
  · exact box_ok66
  · exact box_ok67
  · exact box_ok68
  · exact box_ok69
  · exact box_ok70
  · exact box_ok71
  · exact box_ok72
  · exact box_ok73
  · exact box_ok74
  · exact box_ok75
  · exact box_ok76
  · exact box_ok77
  · exact box_ok78
  · exact box_ok79
  · exact box_ok80
  · exact box_ok81
  · exact box_ok82
  · exact box_ok83
  · exact box_ok84
  · exact box_ok85
  · exact box_ok86
  · exact box_ok87
  · exact box_ok88
  · exact box_ok89
  · exact box_ok90
  · exact box_ok91
  · exact box_ok92
  · exact box_ok93
  · exact box_ok94
  · exact box_ok95
end PetersenNegated3971
