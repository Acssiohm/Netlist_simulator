## Difficultés
- Pour gérer la mémoire dans le scheduler, la seule chose dont dépends la valeur d'une RAM/ROM est l'adresse de lecture read_addr
- On a les registres et les variables dans le même dictionnaire ("vars") la différence étant le moment où elles sont mises à jour 
- Pendant l'exécution des équations, on n'écrit pas dans les mémoire ( on ne les met à jour qu'à la fin du cycle ) ainsi l'instruction REG ne fait rien car la valeur reste celle de l'écriture au cycle précédent, et RAM ne fait qu'accéder à la valeur à l'adresse read_addr

## Choix particulier & Utilisation
- Attention les valeurs ( même les adresses ) sont interprétée avec int_of_string, donc par défaut elles sont en base 10 mais il est possible de les écrire en binaire avec le préfixe 0b ou en hexadécimal avec 0x ( tout ce que permet string_of_int ). De même les sorties sont en décimal.
- Un problème dans l'entrée d'une input ( valeur non entière ou qui dépasse les bornes autorisées par le type de l'input ) donne pour l'instant lieu à une erreur non rattrapée, donc faut recommencer
- Lorsqu'il y a des ROMs dans le circuit, les cases sont initialement à 0. Le programme demande ensuite pour chaque ROM, en rappelant : nom, adress size et word size, les adresses que vous souhaitez changer et la nouvelle valeur, pour terminer il suffit de taper autre chose qu'un nombre (en particuluer la touche entrée suffit).

## Compilation & Exécution
Rien ne change par rapport à ce qui est décrit dans tp1.pdf car le squelette du code n'a pas été changé.

Compilation :
`make build`

Execution :
`./netlist_simulator.byte [-n nombre_de_cycle] fichier_netlist.net`
OU
`make fichier_netlist`

par exemple, pour tester le nadder : 
`./netlist_simulator.byte ./test/nadder.net`
et
`make ./test/nadder`
sont équivalent.
