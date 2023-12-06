(ns gdl.graphics
  (:import com.badlogic.gdx.Gdx))

(defn screen-width  [] (.getWidth           Gdx/graphics))
(defn screen-height [] (.getHeight          Gdx/graphics))
(defn fps           [] (.getFramesPerSecond Gdx/graphics))
