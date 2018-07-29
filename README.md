# hilecop (consulté/modifé DA)

Projet (actuel) : 

Animateur de réseaux de Petri (temporels et un peu interprétés) exécutés en synchrone, certifié avec Coq.

Description :

SPN.v traite des réseaux de Petri généralisés étendus (i.e. avec des arcs test et inhibiteur) exécutés en synchrone.
STPN.v  rajoute la dimension temporel pour animer des réseaux de Petri temporels exécutés en synchrone.
SITPN.v  rajoute une partie de l'interprétation : l'influence de l'environnement sur la possibilité ou non de déclencher les transitions.

Architecture du dépôt :

- src/ : fichiers SPN.v  STPN. et SITPN.v  avec des exemples dans  3 fichiers correspondants (*_examples.v).

Beaucoup de fichiers PDF récoltés sur le Web (tutoriels Coq, thèses en rapport avec Coq ou Hilecop, articles de recherches)
  
Execution sur Linux : 
- Télécharger le dépôt Git (Download ZIP sur la page GitHub) et le décompresser à l'endroit de votre choix.
- Aller dans le dossier '<your_path_to_repo>/hilecop/src/' 
- Lancer la commande suivante : 
>> make 

ceci pour construire les .vo qui entrent en jeux pour les dépendances ("Import ... ") et effectuer les tests dans les 3 *_examples.v


Si rajout de .v, les ajouter aussi dans _CoqProject et utiliser la commande :
>> coq_makefile -f _CoqProject -o Makefile

pour construire le Makefile désiré, avant de faire "make".
