(ns gdl.backends.libgdx.context.graphics
  (:require [gdl.graphics.color :as color])
  (:import com.badlogic.gdx.graphics.Color))

(do
  (.bindRoot #'color/white  Color/WHITE)
  (.bindRoot #'color/black  Color/BLACK)
  (.bindRoot #'color/gray   Color/GRAY)
  (.bindRoot #'color/yellow Color/YELLOW)
  (.bindRoot #'color/red    Color/RED)
  (.bindRoot #'color/green  Color/GREEN)
  (.bindRoot #'color/orange Color/ORANGE))
