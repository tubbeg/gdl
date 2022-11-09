(ns engine.utils
  (:import java.util.zip.ZipInputStream))

(defn set-var-root [v value]
  (alter-var-root v (constantly value)))

; http://stackoverflow.com/questions/1429172/list-files-inside-a-jar-file
(defn get-jar-entries [filter-predicate] ; TODO ?
  (let [src (.getCodeSource (.getProtectionDomain engine.GradientSprite))
        zip (ZipInputStream. (.openStream (.getLocation src)))]
    (loop [entry (.getNextEntry zip)
           hits []]
      (if entry
        (recur (.getNextEntry zip)
               (let [entryname (.getName entry)]
                 (if (filter-predicate entryname)
                   (conj hits entryname)
                   hits)))
        hits))))
