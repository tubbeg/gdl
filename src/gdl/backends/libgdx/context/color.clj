(ns gdl.backends.libgdx.context.color
  (:require [gdl.context :refer [Graphics ->color]]
            [gdl.graphics.color :as color])
  (:import com.badlogic.gdx.graphics.Color))

(extend-type gdl.context.Context
  Graphics
  (->color
    ([_ r g b]
     (->color r g b 1))
    ([_ r g b a]
     (Color. (float r) (float g) (float b) (float a)))))

(defn load-color-vars! []
  (.bindRoot #'color/white  Color/WHITE)
  (.bindRoot #'color/black  Color/BLACK)
  (.bindRoot #'color/gray   Color/GRAY)
  (.bindRoot #'color/yellow Color/YELLOW)
  (.bindRoot #'color/red    Color/RED)
  (.bindRoot #'color/green  Color/GREEN)
  (.bindRoot #'color/orange Color/ORANGE))
