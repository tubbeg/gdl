(ns gdl.render
  (:require [gdl.graphics.batch :refer [batch]]
            [gdl.graphics.shape-drawer :as shape-drawer])
  (:import (com.badlogic.gdx.graphics Color OrthographicCamera)))

(defn render-with [unit-scale ^OrthographicCamera camera renderfn]
  (shape-drawer/set-line-width unit-scale)
  (.setColor batch Color/WHITE) ; fix scene2d.ui.tooltip flickering
  (.setProjectionMatrix batch (.combined camera))
  (.begin batch)
  (renderfn unit-scale)
  (.end batch))
