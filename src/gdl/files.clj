(ns gdl.files
  (:require [clojure.string :as str])
  (:import com.badlogic.gdx.Gdx
           com.badlogic.gdx.files.FileHandle))

(defn internal ^FileHandle [file]
  (.internal Gdx/files file))

(defn ^:no-doc recursively-search-files [folder extensions]
  (loop [[^FileHandle file & remaining] (.list (internal folder))
         result []]
    (cond (nil? file)
          result

          (.isDirectory file)
          (recur (concat remaining (.list file)) result)

          (extensions (.extension file))
          (recur remaining (conj result (str/replace-first (.path file) folder "")))

          :else
          (recur remaining result))))
