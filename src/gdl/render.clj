(ns gdl.render
  (:require [gdl.graphics.color :as color]
            [gdl.graphics.unit-scale :refer [*unit-scale*]]
            [gdl.graphics.batch :refer [batch]]
            [gdl.graphics.shape-drawer :as shape-drawer])
  (:import com.badlogic.gdx.graphics.OrthographicCamera))

(defn render-with [unit-scale ^OrthographicCamera camera renderfn]
  (binding [*unit-scale* unit-scale]
    (shape-drawer/set-line-width! *unit-scale*)
    (.setColor batch color/white) ; fix scene2d.ui.tooltip flickering
    (.setProjectionMatrix batch (.combined camera))
    (.begin batch)
    (renderfn)
    (.end batch)))
