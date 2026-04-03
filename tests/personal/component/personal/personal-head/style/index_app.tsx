
import { Platform, StyleSheet } from 'react-native';
import { SuitStyle, PlatformUtils } from '@hw-vmall/vrn-basic-comp';
export interface PerosonHead {
  [propName: string]: any;
}
export default (theme, isPad, isShow, newMergeStyle, isMember) => {
  if (newMergeStyle) {
    theme = SuitStyle;
  }
  const topBoxHeaderPadding = isPad ? 24 : 16;
  const userNameTextColor = isMember ? theme.C17 : theme.C11;
  const margin = isPad ? 24 : 16;
  // 左侧标题高度 = 用户名行高 + 用户等级高度
  const headerHeight = 21 + 17 * 0.8;
  return StyleSheet.create<PerosonHead>({
    View: {
      display: 'flex',
      flexDirection: 'row',
      alignItems: 'center',
      justifyContent: 'space-between',
      marginBottom: 8,
      backgroundColor: '#F1F3F5',
    },
    myTitle: {
      fontSize: 26,
      lineHeight: 32,
      color: 'rgba(0,0,0,0.90)',
      fontWeight: '700',
      paddingTop: 1.5,
    },
    topBoxHeader: {
      paddingHorizontal: !isShow ? 0 : topBoxHeaderPadding,
    },

    cricle: {
      marginRight: 7,
      position: 'relative',
      alignContent: 'center',
      alignItems: 'center',
      justifyContent: 'center',
      width: 32,
      height: 32,
    },
    view: {
      height: 56,
      flexDirection: 'row',
      display: 'flex',
      position: 'relative',
      alignItems: 'center',
      justifyContent: 'space-between',
    },
    topIcon: {
      position: 'absolute',
      top: -4,
      right: -4,
      width: 16,
      height: 16,
      borderRadius: 8,
      backgroundColor: theme.C35.color,
    },
    avartWrap: {
      height: 32,
      flex: 1,
      display: 'flex',
      flexDirection: 'row',
      alignItems: 'center',
      justifyContent: 'flex-start',
      marginLeft: !isShow ? 0 : margin,
      marginRight: 24,
    },
    userAva: { width: 32, height: 32, borderRadius: 16, marginRight: 16 },
    userName: {
      ...theme.T10,
      ...userNameTextColor,
      marginRight: 3,
      fontSize: 16,
      color: 'rgba(0,0,0,0.90)',
      fontWeight: '500',
    },
    userNameBox: {
      position: 'absolute',
      left: 20,
    },
    userNameBoxView: {
      display: 'flex',
      flexDirection: 'column',
      justifyContent: 'flex-start',
      flex: 1,
    },
    appMemberLoginHeader: {
      justifyContent: 'center',
    },
    iconList: {
      display: 'flex',
      flexDirection: 'row',
      alignItems: 'center',
      justifyContent: 'flex-start',
      marginRight: !isShow ? 0 : margin,
    },
    image: {
      width: 40,
      height: 40,
      alignItems: 'center',
      justifyContent: 'center',
    },
    imageLast: {
      marginRight: 0,
    },
    text: {
      ...theme.T13,
      ...theme.C11,
    },
    rightWrap: {
      height: '100%',
      justifyContent: 'flex-end',
      maxWidth: 120,
    },
    rightText: {
      ...theme.T7,
    },
    topText: {
      ...theme.T1,
      ...theme.C17,
      textAlign: 'center',
      lineHeight: 16,
    },
    hidden: {
      display: 'none',
      position: 'relative',
    },
    topIconMore: {
      width: 24,
    },
    bgImageView: {
      overflow: 'hidden',
      width: '100%',
    },
    showText: {
      ...theme.T0,
      fontSize: 8,
      fontWeight: '400',
      maxWidth: 16,
      height: 10,
      transform: [{ scale: 8 / 12 }],
      bottom: 0.5,
      color: 'black',
      justifyContent: 'center',
      alignItems: 'center',
      lineHeight: Platform.OS === 'ios' ? 12 : 11.5,
    },
    showIcon: {
      width: 7,
      height: 7,
      zIndex: 1,
    },
    showAvatar: {
      height: 9,
      backgroundColor: '#FFDDA9',
      borderRadius: 6,
      bottom: -30,
      zIndex: 100,
      justifyContent: 'center',
      alignItems: 'center',
      flexDirection: 'row',
      paddingLeft: 1,
      paddingRight: 1,
      position: 'relative',
    },
    showRadius: {
      position: 'absolute',
      width: 32,
      height: 34,
      zIndex: 99,
    },
    avaImg: {
      width: 32,
      height: 32,
      borderRadius: 24,
      zIndex: 1,
      top: -5,
      left: 0,
      overflow: 'hidden',
    },
    tagText: {
      display: 'flex',
      flexDirection: 'row',
      alignItems: 'center',
    },
    medal: {
      width: 14 * 0.8,
      height: 17 * 0.8,
    },
    txtBg: {
      height: 13 * 0.8,
      backgroundColor: 'rgba(249,188,100,0.2)',
      paddingRight: 3 * 0.8,
      paddingLeft: 7 * 0.8,
      borderTopRightRadius: 7.5 * 0.8,
      borderBottomRightRadius: 7.5 * 0.8,
      marginLeft: -6 * 0.8,
      paddingTop: isPad && PlatformUtils.isHarmony() ? 1 * 0.8 : 0,
    },
    tagTxt: {
      fontSize: 9 * 0.8,
      color: '#825B44',
      letterSpacing: 0.3,
      ...(PlatformUtils.isHarmony() ? { lineHeight: 13 * 0.8 } : {}),
    },
    unLoginHeader: { position: 'relative', justifyContent: 'center', width: '100%' },
    headerImg: { position: 'absolute', top: (headerHeight - 32) / 2 },
    headerMemberImg: { position: 'absolute', top: (headerHeight - 38) / 2 },
    loginHeader: { position: 'relative', justifyContent: 'center', height: headerHeight },
  });
};
